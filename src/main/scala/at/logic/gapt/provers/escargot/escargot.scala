package at.logic.gapt.provers.escargot

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

trait TermOrdering {
  def lt( e1: LambdaExpression, e2: LambdaExpression ): Boolean
}

case class LPO( precedence: Seq[Const], typeOrder: Set[( Ty, Ty )] ) extends TermOrdering {
  val precIdx: Map[Const, Int] = precedence.zipWithIndex.toMap

  def lt( e1: LambdaExpression, e2: LambdaExpression ): Boolean = {
    val memo = mutable.Map[( LambdaExpression, LambdaExpression ), Boolean]()

    def memoLt( e1: LambdaExpression, e2: LambdaExpression ): Boolean =
      memo.getOrElseUpdate( ( e1, e2 ), e2 match {
        case _ if typeOrder( e1.exptype, e2.exptype ) => true
        case Apps( c2: Const, as2 ) =>
          if ( as2 contains e1 ) return true
          if ( as2 exists { memoLt( e1, _ ) } ) return true
          e1 match {
            case Apps( c1: Const, as1 ) =>
              ( precIdx get c1, precIdx get c2 ) match {
                case ( Some( i1 ), Some( i2 ) ) if i1 < i2 => as1.forall { memoLt( _, e2 ) }
                case _ if c1 == c2 =>
                  def lex( as1: List[LambdaExpression], as2: List[LambdaExpression] ): Boolean =
                    ( as1, as2 ) match {
                      case ( a1 :: as1_, a2 :: as2_ ) if a1 == a2 => lex( as1_, as2_ )
                      case ( a1 :: as1_, a2 :: as2_ ) if memoLt( a1, a2 ) => as1_ forall { memoLt( _, e2 ) }
                      case _ => false
                    }
                  lex( as1, as2 )
                case _ => false
              }
            case _ => false
          }
        case _ => false
      } )

    memoLt( e1, e2 )
  }
}

case class KBO( precedence: Seq[Const], constWeights: Map[Const, Int] = Map() ) extends TermOrdering {
  val precIdx: Map[Const, Int] = precedence.zipWithIndex.toMap
  val varWeight = ( constWeights.filterKeys { arity( _ ) == 1 }.values.toSet + 1 ).min

  def lt( e1: LambdaExpression, e2: LambdaExpression ): Boolean = {
    val w1 = weight( e1 )
    val w2 = weight( e2 )

    if ( w1 > w2 ) return false
    if ( occs( e1 ) diff occs( e2 ) nonEmpty ) return false

    if ( w1 < w2 ) return true

    ( e1, e2 ) match {
      case ( Apps( c1: Const, as1 ), Apps( c2: Const, as2 ) ) =>
        def lex( as1: List[LambdaExpression], as2: List[LambdaExpression] ): Boolean =
          ( as1, as2 ) match {
            case ( a1 :: as1_, a2 :: as2_ ) if a1 == a2 => lex( as1_, as2_ )
            case ( a1 :: as1_, a2 :: as2_ ) if lt( a1, a2 ) => true
            case _ => false
          }

        ( precIdx get c1, precIdx get c2 ) match {
          case ( ( Some( i1 ), Some( i2 ) ) ) if i1 < i2 => true
          case _ if c1 == c2                             => lex( as1, as2 )
          case _                                         => false
        }

      case _ => false
    }
  }

  def occs( expr: LambdaExpression ): Seq[Var] = {
    val r = Seq.newBuilder[Var]
    def f( e: LambdaExpression ): Unit = e match {
      case App( a, b ) =>
        f( a ); f( b )
      case v: Var => r += v
      case _      =>
    }
    f( expr )
    r.result()
  }

  def weight( expr: LambdaExpression ): Int = expr match {
    case c: Const           => constWeights.getOrElse( c, 1 )
    case v: Var             => varWeight
    case Apps( head, args ) => weight( head ) + args.map( weight ).sum
  }
}

class EscargotLoop extends Logger {
  var termOrdering: TermOrdering = _
  var hasEquality = true

  private var clsIdx = 0
  class Cls( val proof: ResolutionProof ) {
    val index = { clsIdx += 1; clsIdx }
    def clause = proof.conclusion

    val maximal = for {
      ( a, i ) <- clause.zipWithIndex.elements
      if !clause.elements.exists { x => a != x && termOrdering.lt( a, x ) }
    } yield i

    val selected = ( maximal.filter { _.isAnt } ++ clause.indicesSequent.antecedent ).take( 1 )

    val weight = clause.elements.map { expressionSize( _ ) }.sum

    override def toString = s"[$index] $clause   (max = ${maximal mkString ", "}) (sel = ${selected mkString ", "})"
    override def hashCode = index
  }

  var newlyDerived = mutable.Set[Cls]()
  val usable = mutable.Set[Cls]()
  val workedOff = mutable.Set[Cls]()
  val demodulators = mutable.Set[Cls]()

  def preprocessing() = {
    deleteDuplicates()
    if ( hasEquality ) simplifyNew()
    tautologyDeletion()
    if ( hasEquality ) equalityResolution()
    if ( hasEquality ) reflexivityDeletion()
    factorClauses()
    deleteDuplicates()
    subsumptionDeletion()
  }

  def deleteDuplicates() =
    for ( ( _, group ) <- newlyDerived groupBy { _.clause } )
      newlyDerived --= group.tail

  def factorClauses() =
    newlyDerived = newlyDerived map { cls =>
      val factored = Factor( cls.proof )._1
      if ( factored.conclusion == cls.proof.conclusion )
        cls
      else
        new Cls( Factor( cls.proof )._1 )
    }

  def tautologyDeletion() =
    newlyDerived = newlyDerived filterNot { _.clause.isTaut }

  def reflexivityDeletion() =
    newlyDerived = newlyDerived filterNot { _.clause.succedent.collect { case Eq( t, t_ ) if t == t_ => () }.nonEmpty }

  def equalityResolution() =
    newlyDerived = newlyDerived map { cls =>
      val refls = cls.clause.antecedent collect { case Eq( t, t_ ) if t == t_ => t }
      new Cls( refls.foldRight( cls.proof )( ( t, proof ) =>
        Resolution( ReflexivityClause( t ), Suc( 0 ), proof, proof.conclusion.indexOfInAnt( t === t ) ) ) )
    }

  def collectDemodulator( cls: Cls ) =
    cls.clause match {
      case Sequent( Seq(), Seq( Eq( t, s ) ) ) if termOrdering.lt( s, t ) =>
        debug( s"demodulator: $t -> $s" )
        demodulators += cls
        simplify()
      case Sequent( Seq(), Seq( Eq( s, t ) ) ) if termOrdering.lt( s, t ) =>
        debug( s"demodulator: $s -> $t" )
        val newCls = new Cls( Flip( cls.proof, Suc( 0 ) ) )
        workedOff -= cls
        workedOff += newCls
        demodulators += newCls
        simplify()
      case _ => ()
    }

  def simplify(): Unit =
    for {
      store <- Seq( newlyDerived, usable, workedOff )
      cls <- store
      if !demodulators.contains( cls )
      if simplify( cls )
    } store -= cls

  def simplifyNew(): Unit =
    for ( cls <- newlyDerived if simplify( cls ) ) newlyDerived -= cls

  def simplify( cls: Cls ): Boolean = {
    def doSimp( p: ResolutionProof, didAlreadySimplify: Boolean ): Boolean = {
      for {
        i <- p.conclusion.indices; pos <- LambdaPosition getPositions p.conclusion( i )
        t_ = p.conclusion( i )( pos )
        demod <- demodulators; Eq( t, s ) <- demod.clause
        subst <- syntacticMatching( t, t_ )
      } return doSimp( Paramodulation(
        Instance( demod.proof, subst ), Suc( 0 ),
        p, i,
        Seq( pos ), leftToRight = true
      ), didAlreadySimplify = true )

      if ( didAlreadySimplify ) newlyDerived += new Cls( p )
      didAlreadySimplify
    }

    doSimp( cls.proof, didAlreadySimplify = false )
  }

  def clauseProcessing() = {
    usable ++= newlyDerived
    newlyDerived.clear()
  }

  def subsumptionDeletion() =
    for {
      cls1 <- newlyDerived
      cls2 <- newlyDerived if cls1 != cls2
      if newlyDerived contains cls1
      _ <- clauseSubsumption( cls2.clause, cls1.clause )
    } newlyDerived -= cls1

  def forwardSubsumption() =
    for {
      existing <- workedOff
      cls <- newlyDerived
      _ <- clauseSubsumption( existing.clause, cls.clause )
    } newlyDerived -= cls

  def backwardSubsumption( given: Cls ) =
    for {
      existing <- workedOff
      _ <- clauseSubsumption( given.clause, existing.clause )
    } workedOff -= existing

  def inferenceComputation( given: Cls ) = {
    if ( hasEquality ) collectDemodulator( given )

    orderedResolution( given )
    if ( hasEquality ) orderedParamodulation( given )
    factoring( given )
    if ( hasEquality ) unifyingEqualityResolution( given )
  }

  def factoring( given: Cls ): Unit =
    for {
      i <- given.maximal; j <- given.maximal
      if i < j && i.sameSideAs( j )
      mgu <- syntacticMGU( given.clause( i ), given.clause( j ) )
    } newlyDerived += new Cls( Instance( given.proof, mgu ) )

  def unifyingEqualityResolution( given: Cls ): Unit =
    for {
      i <- given.maximal if i.isAnt
      Eq( t, s ) <- Some( given.clause( i ) )
      mgu <- syntacticMGU( t, s )
    } newlyDerived += new Cls( Instance( given.proof, mgu ) )

  def orderedResolution( given: Cls ): Unit =
    for ( existing <- workedOff ) {
      orderedResolution( given, existing )
      orderedResolution( existing, given )
    }

  def orderedResolution( c1: Cls, c2: Cls ): Unit = {
    if ( c2.selected.nonEmpty ) return
    val renaming = Substitution( rename( freeVariables( c2.clause ), freeVariables( c1.clause ) ) )
    val p2_ = Instance( c2.proof, renaming )
    for {
      i1 <- if ( c1.selected.nonEmpty ) c1.selected else c1.maximal
      a1 = c1.clause( i1 ) if i1 isAnt;
      i2 <- c2.maximal if i2 isSuc;
      mgu <- syntacticMGU( p2_.conclusion( i2 ), a1 )
      if c1.selected.nonEmpty || !c1.maximal.exists { i1_ => i1_ != i1 && termOrdering.lt( a1, mgu( c1.clause( i1_ ) ) ) }
      if !c2.maximal.exists { i2_ => i2_ != i2 && termOrdering.lt( mgu( p2_.conclusion( i2 ) ), mgu( p2_.conclusion( i2_ ) ) ) }
      ( p1__, conn1 ) = Factor( Instance( c1.proof, mgu ) )
      ( p2__, conn2 ) = Factor( Instance( p2_, mgu ) )
    } newlyDerived += new Cls( Resolution( p2__, conn2 child i2, p1__, conn1 child i1 ) )
  }

  def orderedParamodulation( given: Cls ): Unit =
    for ( existing <- workedOff ) {
      orderedParamodulation( given, existing )
      orderedParamodulation( existing, given )
    }

  def orderedParamodulation( c1: Cls, c2: Cls ): Unit = {
    if ( c1.selected.nonEmpty ) return
    val renaming = Substitution( rename( freeVariables( c2.clause ), freeVariables( c1.clause ) ) )
    val p2_ = Instance( c2.proof, renaming )

    def isReductive( atom: HOLFormula, i: SequentIndex, pos: LambdaPosition ): Boolean =
      ( atom, i, pos.toList ) match {
        case ( Eq( t, s ), _: Suc, 2 :: _ )      => !termOrdering.lt( s, t )
        case ( Eq( t, s ), _: Suc, 1 :: 2 :: _ ) => !termOrdering.lt( t, s )
        case _                                   => true
      }

    for {
      i1 <- c1.maximal; Eq( t, s ) <- Some( c1.clause( i1 ) ) if i1.isSuc
      ( t_, s_, leftToRight ) <- Seq( ( t, s, true ), ( s, t, false ) ) if !termOrdering.lt( t_, s_ )
      i2 <- if ( c2.selected.nonEmpty ) c2.selected else c2.maximal
      a2 = p2_.conclusion( i2 )
      pos2 <- LambdaPosition.getPositions( a2 ) if !a2( pos2 ).isInstanceOf[Var]
      mgu <- syntacticMGU( t_, a2( pos2 ) )
      if !termOrdering.lt( mgu( t_ ), mgu( s_ ) )
      if isReductive( mgu( a2 ), i2, pos2 )
      p1__ = Instance( c1.proof, mgu )
      p2__ = Instance( p2_, mgu )
    } newlyDerived += new Cls( Paramodulation( p1__, i1, p2__, i2, Seq( pos2 ), leftToRight ) )
  }

  def isSubsumedByWorkedOff( given: Cls ) =
    workedOff exists { cls => clauseSubsumption( cls.clause, given.clause ) isDefined }

  def loop(): Option[ResolutionProof] = {
    preprocessing()

    clauseProcessing()
    while ( usable.nonEmpty ) {
      for ( cls <- usable if cls.clause.isEmpty )
        return Some( cls.proof )

      val given = usable.minBy { _.weight }
      usable -= given

      if ( !isSubsumedByWorkedOff( given ) ) {
        backwardSubsumption( given )
        workedOff += given

        debug( s"[wo=${workedOff.size},us=${usable.size}] given: $given" )
        inferenceComputation( given )

        preprocessing()
        forwardSubsumption()

        clauseProcessing()
      }
    }

    None
  }
}

object Escargot extends Escargot {
  def lpoHeuristic( cnf: Traversable[HOLClause] ): LPO = {
    val consts = constants( cnf flatMap { _.elements } )

    val boolOnTermLevel = consts exists { case Const( _, FunctionType( _, from ) ) => from contains To }
    val types = consts flatMap { c => baseTypes( c.exptype ) }

    val atoms = for ( c <- consts; FunctionType( to, _ ) = c.exptype if to == To ) yield c
    val functions = for ( c <- consts; FunctionType( to, _ ) = c.exptype if to != To ) yield c

    val precedence = functions.toSeq.sortBy { arity( _ ) } ++ atoms.toSeq.sortBy { arity( _ ) }

    LPO( precedence, if ( boolOnTermLevel ) Set() else ( types - To ) map { ( _, To ) } )
  }
}

class Escargot extends ResolutionProver {
  override def getRobinsonProof( cnf: Traversable[HOLClause] ): Option[ResolutionProof] = {
    val loop = new EscargotLoop
    loop.hasEquality = cnf.flatMap( _.elements ).exists { case Eq( _, _ ) => true; case _ => false }
    loop.termOrdering = Escargot.lpoHeuristic( cnf )
    loop.newlyDerived ++= cnf.map { cls => new loop.Cls( InputClause( cls ) ) }
    loop.loop()
  }
}
