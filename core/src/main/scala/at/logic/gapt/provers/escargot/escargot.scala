package at.logic.gapt.provers.escargot

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

trait TermOrdering {
  def lt( e1: LambdaExpression, e2: LambdaExpression ): Boolean = lt( e1, e2, treatVarsAsConsts = false )
  def lt( e1: LambdaExpression, e2: LambdaExpression, treatVarsAsConsts: Boolean ): Boolean
}

case class LPO( precedence: Seq[Const] = Seq(), typeOrder: Set[( Ty, Ty )] = Set() ) extends TermOrdering {
  val precIdx: Map[Const, Int] = precedence.zipWithIndex.toMap

  def lt( e1: LambdaExpression, e2: LambdaExpression, treatVarsAsConsts: Boolean ): Boolean = {
    val memo = mutable.Map[( LambdaExpression, LambdaExpression ), Boolean]()

    def precLt( h1: LambdaExpression, h2: LambdaExpression ) =
      ( h1, h2 ) match {
        case ( c1: Const, c2: Const )                  => precIdx.getOrElse( c1, -1 ) < precIdx.getOrElse( c2, -1 )
        case ( _: Var, _: Const ) if treatVarsAsConsts => true
        case ( v1: Var, v2: Var ) if treatVarsAsConsts => v1.toString < v2.toString
        case _                                         => false
      }

    def memoLt( e1: LambdaExpression, e2: LambdaExpression ): Boolean =
      memo.getOrElseUpdate( ( e1, e2 ), typeOrder( e1.exptype, e2.exptype ) || {
        val Apps( c1, as1 ) = e1
        val Apps( c2, as2 ) = e2
        if ( as2 contains e1 ) true
        else if ( as2 exists { memoLt( e1, _ ) } ) true
        else if ( precLt( c1, c2 ) ) as1.forall { memoLt( _, e2 ) }
        else if ( c1 == c2 ) {
          def lex( as1: List[LambdaExpression], as2: List[LambdaExpression] ): Boolean =
            ( as1, as2 ) match {
              case ( a1 :: as1_, a2 :: as2_ ) if a1 == a2 => lex( as1_, as2_ )
              case ( a1 :: as1_, a2 :: as2_ ) if memoLt( a1, a2 ) => as1_ forall { memoLt( _, e2 ) }
              case _ => false
            }
          lex( as1, as2 )
        } else false
      } )

    memoLt( e1, e2 )
  }
}

case class KBO( precedence: Seq[Const], constWeights: Map[Const, Int] = Map() ) extends TermOrdering {
  val precIdx: Map[Const, Int] = precedence.zipWithIndex.toMap
  val varWeight = ( constWeights.filterKeys { arity( _ ) == 1 }.values.toSet + 1 ).min

  def lt( e1: LambdaExpression, e2: LambdaExpression, treatVarsAsConsts: Boolean ): Boolean = {
    val w1 = weight( e1 )
    val w2 = weight( e2 )

    if ( w1 > w2 ) return false
    if ( !treatVarsAsConsts ) if ( occs( e1 ) diff occs( e2 ) nonEmpty ) return false

    if ( w1 < w2 ) return true

    val Apps( c1, as1 ) = e1
    val Apps( c2, as2 ) = e2

    def lex( as1: List[LambdaExpression], as2: List[LambdaExpression] ): Boolean =
      ( as1, as2 ) match {
        case ( a1 :: as1_, a2 :: as2_ ) if a1 == a2 => lex( as1_, as2_ )
        case ( a1 :: as1_, a2 :: as2_ ) if lt( a1, a2, treatVarsAsConsts ) => true
        case _ => false
      }

    val precLt = ( c1, c2 ) match {
      case ( c1: Const, c2: Const )                  => precIdx.getOrElse( c1, -1 ) < precIdx.getOrElse( c2, -1 )
      case ( _: Var, _: Const ) if treatVarsAsConsts => true
      case ( v1: Var, v2: Var ) if treatVarsAsConsts => v1.toString < v2.toString
      case _                                         => false
    }

    if ( precLt ) true
    else if ( c1 == c2 ) lex( as1, as2 )
    else false
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
  var termOrdering: TermOrdering = LPO()
  var hasEquality = true

  class Cls( val proof: ResolutionProof, val index: Int ) {
    def clause = proof.conclusion

    val maximal = for {
      ( a, i ) <- clause.zipWithIndex.elements
      if !clause.elements.exists { x => a != x && termOrdering.lt( a, x ) }
    } yield i

    val selected = ( maximal.filter { _.isAnt } ++ clause.indicesSequent.antecedent ).take( 1 )

    val weight = clause.elements.map { expressionSize( _ ) }.sum

    override def toString = s"[$index] $clause   (max = ${maximal mkString ", "}) (sel = ${selected mkString ", "}) (w = $weight)"
    override def hashCode = index
  }

  private var clsIdx = 0
  def InputCls( clause: HOLClause ): Cls = { clsIdx += 1; new Cls( InputClause( clause ), clsIdx ) }
  def SimpCls( parent: Cls, newProof: ResolutionProof ): Cls = new Cls( newProof, parent.index )
  def DerivedCls( parent: Cls, newProof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( newProof, clsIdx ) }
  def DerivedCls( parent1: Cls, parent2: Cls, newProof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( newProof, clsIdx ) }

  var newlyDerived = mutable.Set[Cls]()
  val usable = mutable.Set[Cls]()
  val workedOff = mutable.Set[Cls]()

  def preprocessing() = {
    deleteDuplicates()
    if ( hasEquality ) unitRewriteNew()
    if ( hasEquality ) orderEquations()
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

  def unitRewriteNew() =
    for ( cls <- newlyDerived if unitRewriting( workedOff, cls ) )
      newlyDerived -= cls

  def orderEquations() =
    newlyDerived = newlyDerived map { cls =>
      val toFlip = cls.clause filter {
        case Eq( t, s ) => termOrdering.lt( s, t )
        case _          => false
      }
      var p = cls.proof
      for ( e <- toFlip ) p = Flip( p, p.conclusion indexOf e )
      SimpCls( cls, p )
    }

  def factorClauses() =
    newlyDerived = newlyDerived map { cls =>
      SimpCls( cls, Factor( cls.proof )._1 )
    }

  def tautologyDeletion() =
    newlyDerived = newlyDerived filterNot { _.clause.isTaut }

  def reflexivityDeletion() =
    newlyDerived = newlyDerived filterNot { _.clause.succedent.collect { case Eq( t, t_ ) if t == t_ => () }.nonEmpty }

  def equalityResolution() =
    newlyDerived = newlyDerived map { cls =>
      val refls = cls.clause.antecedent collect { case Eq( t, t_ ) if t == t_ => t }
      SimpCls( cls, refls.foldRight( cls.proof )( ( t, proof ) =>
        Resolution( ReflexivityClause( t ), Suc( 0 ), proof, proof.conclusion.indexOfInAnt( t === t ) ) ) )
    }

  def canonize( expr: LambdaExpression ): LambdaExpression = {
    val eqs = for {
      c <- workedOff
      Sequent( Seq(), Seq( Eq( t, s ) ) ) <- Seq( c.clause )
      if syntacticMatching( t, s ).isDefined
      if syntacticMatching( s, t ).isDefined
      ( t_, s_, leftToRight ) <- Seq( ( t, s, true ), ( s, t, false ) )
      if !termOrdering.lt( t_, s_ )
    } yield ( t_, s_, c, leftToRight )
    if ( eqs isEmpty ) return expr

    var e = expr
    var didRewrite = true
    while ( didRewrite ) {
      didRewrite = false
      for {
        ( subterm, pos ) <- LambdaPosition getPositions e groupBy { e( _ ) } if !didRewrite
        if !subterm.isInstanceOf[Var]
        ( t_, s_, c1, leftToRight ) <- eqs if !didRewrite
        subst <- syntacticMatching( t_, subterm )
        if termOrdering.lt( subst( s_ ), subterm, treatVarsAsConsts = true )
      } {
        for ( p <- pos ) e = e.replace( p, subst( s_ ) )
        didRewrite = true
      }
    }
    e
  }

  def isReflModE( cls: Cls ) =
    cls.clause.succedent exists {
      case Eq( t, s ) => canonize( t ) == canonize( s )
      case _          => false
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

  def inferenceComputation( given: Cls ): Unit = {
    if ( hasEquality ) {
      unitRewriting( given )
      if ( !workedOff.contains( given ) )
        return
    }

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
    } newlyDerived += DerivedCls( given, Instance( given.proof, mgu ) )

  def unifyingEqualityResolution( given: Cls ): Unit =
    for {
      i <- given.maximal if i.isAnt
      Eq( t, s ) <- Some( given.clause( i ) )
      mgu <- syntacticMGU( t, s )
    } newlyDerived += DerivedCls( given, Instance( given.proof, mgu ) )

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
    } newlyDerived += DerivedCls( c1, c2, Resolution( p2__, conn2 child i2, p1__, conn1 child i1 ) )
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
      ( st2, pos2 ) <- LambdaPosition getPositions a2 groupBy { a2( _ ) }
      if !st2.isInstanceOf[Var]
      mgu <- syntacticMGU( t_, st2 )
      if !termOrdering.lt( mgu( t_ ), mgu( s_ ) )
      pos2_ = pos2 filter { isReductive( mgu( a2 ), i2, _ ) } if pos2_.nonEmpty
      p1__ = Instance( c1.proof, mgu )
      p2__ = Instance( p2_, mgu )
    } newlyDerived += DerivedCls( c1, c2, Paramodulation( p1__, i1, p2__, i2, pos2_.toSeq, leftToRight ) )
  }

  def unitRewriting( given: Cls ): Unit = {
    if ( unitRewriting( workedOff - given, given ) )
      workedOff -= given
    else
      for ( existing <- workedOff if existing != given if unitRewriting( Some( given ), existing ) )
        workedOff -= existing
  }

  def unitRewriting( cs: Traversable[Cls], c2: Cls ): Boolean = {
    val eqs = for {
      c <- cs
      Sequent( Seq(), Seq( Eq( t, s ) ) ) <- Seq( c.clause )
      ( t_, s_, leftToRight ) <- Seq( ( t, s, true ), ( s, t, false ) )
      if !t_.isInstanceOf[Var]
      if !termOrdering.lt( t_, s_ )
    } yield ( t_, s_, c, leftToRight )
    if ( eqs isEmpty ) return false

    var p = c2.proof
    // Depends on the implementation detail that Paramodulation does not change indices.
    for ( i <- p.conclusion.indices ) {
      var didRewrite = true
      while ( didRewrite ) {
        didRewrite = false
        for {
          ( subterm, pos ) <- LambdaPosition getPositions p.conclusion( i ) groupBy { p.conclusion( i )( _ ) } if !didRewrite
          if !subterm.isInstanceOf[Var]
          ( t_, s_, c1, leftToRight ) <- eqs if !didRewrite
          subst <- syntacticMatching( t_, subterm )
          if termOrdering.lt( subst( s_ ), subterm )
        } {
          p = Paramodulation( Instance( c1.proof, subst ), Suc( 0 ),
            p, i, pos.toSeq, leftToRight )
          didRewrite = true
        }
      }
    }

    if ( p != c2.proof ) {
      newlyDerived += SimpCls( c2, p )
      true
    } else {
      false
    }
  }

  def isSubsumedByWorkedOff( given: Cls ) =
    workedOff exists { cls => clauseSubsumption( cls.clause, given.clause ) isDefined }

  var strategy = 0
  def choose(): Cls = {
    strategy = ( strategy + 1 ) % 6
    if ( strategy < 1 ) usable minBy { _.index }
    else if ( strategy < 3 ) {
      val pos = usable filter { _.clause.antecedent.isEmpty }
      if ( pos isEmpty ) choose()
      else pos minBy { cls => ( cls.weight, cls.index ) }
    } else if ( strategy < 5 ) {
      val nonPos = usable filter { _.clause.antecedent.nonEmpty }
      if ( nonPos isEmpty ) choose()
      else nonPos minBy { cls => ( cls.weight, cls.index ) }
    } else {
      usable minBy { cls => ( cls.weight, cls.index ) }
    }
  }

  def loop(): Option[ResolutionProof] = {
    preprocessing()

    clauseProcessing()

    while ( usable.nonEmpty ) {
      for ( cls <- usable if cls.clause.isEmpty )
        return Some( cls.proof )

      val given = choose()
      usable -= given

      val shouldDiscard = isSubsumedByWorkedOff( given ) || ( hasEquality && isReflModE( given ) )

      debug( s"[wo=${workedOff.size},us=${usable.size}] ${if ( shouldDiscard ) "discarded" else "kept"}: $given" )

      if ( !shouldDiscard ) {
        backwardSubsumption( given )
        workedOff += given

        inferenceComputation( given )

        preprocessing()
        forwardSubsumption()

        clauseProcessing()

        // TODO: check workedOff for isReflModE
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
    loop.newlyDerived ++= cnf.map { loop.InputCls }
    loop.loop()
  }
}
