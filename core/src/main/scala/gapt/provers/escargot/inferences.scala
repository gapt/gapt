package gapt.provers.escargot.impl

import gapt.expr._
import gapt.expr.hol.universalClosure
import gapt.proofs._
import gapt.proofs.resolution._
import gapt.provers.escargot.LPO

import scala.collection.mutable

trait PreprocessingRule {
  def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls]
}

/**
 * An operation that looks at the given clause, and the set of worked off clauses;
 * it returns a set of new clauses, plus a set of clauses that should be discarded.
 */
trait InferenceRule extends PreprocessingRule {
  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] )

  def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls] = {
    val inferred = mutable.Set[Cls]()
    val deleted = mutable.Set[Cls]()

    for ( c <- newlyInferred ) {
      val ( i, d ) = apply( c, existing )
      inferred ++= i
      for ( ( dc, r ) <- d if r subsetOf dc.ass )
        deleted += dc
    }

    newlyInferred -- deleted ++ inferred
  }
}

trait BinaryInferenceRule extends InferenceRule {
  def apply( a: Cls, b: Cls ): Set[Cls]

  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    ( existing.flatMap( apply( given, _ ) ) ++
      existing.flatMap( apply( _, given ) ) ++
      apply( given, given ),
      Set() )
}

trait RedundancyRule extends InferenceRule {
  def isRedundant( given: Cls, existing: Set[Cls] ): Option[Set[Int]]
  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    isRedundant( given, existing ) match {
      case Some( reason ) => ( Set(), Set( given -> reason ) )
      case None           => ( Set(), Set() )
    }
}

trait SimplificationRule extends InferenceRule {
  def simplify( given: Cls, existing: Set[Cls] ): Option[( Cls, Set[Int] )]
  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    simplify( given, existing ) match {
      case Some( ( simplified, reason ) ) => ( Set( simplified ), Set( given -> reason ) )
      case None                           => ( Set(), Set() )
    }
}

object getFOPositions {
  def apply( exp: Expr ): Map[Expr, Seq[LambdaPosition]] = {
    val poss = mutable.Map[Expr, Seq[LambdaPosition]]().withDefaultValue( Seq() )
    def walk( exp: Expr, pos: List[Int] ): Unit = {
      poss( exp ) :+= LambdaPosition( pos.reverse )
      walkApp( exp, pos )
    }
    def walkApp( exp: Expr, pos: List[Int] ): Unit = exp match {
      case App( f, arg ) =>
        walk( arg, 2 :: pos )
        walkApp( f, 1 :: pos )
      case _ =>
    }
    walk( exp, Nil )
    poss.toMap
  }
}

class StandardInferences( state: EscargotState, propositional: Boolean ) {
  import state.{ DerivedCls, SimpCls, termOrdering, nameGen }

  def subsume( a: Cls, b: Cls ): Option[Substitution] =
    fastSubsumption( a.clause, b.clause, a.featureVec, b.featureVec, a.literalFeatureVecs, b.literalFeatureVecs )
  def subsume( a: HOLSequent, b: HOLSequent ): Option[Substitution] =
    if ( propositional ) {
      if ( a isSubMultisetOf b ) Some( Substitution() )
      else None
    } else clauseSubsumption( a, b, multisetSubsumption = true )
  def unify( a: Expr, b: Expr ): Option[Substitution] =
    if ( propositional ) {
      if ( a == b ) Some( Substitution() )
      else None
    } else syntacticMGU( a, b )
  def matching( a: Expr, b: Expr ): Option[Substitution] =
    if ( propositional ) {
      if ( a == b ) Some( Substitution() )
      else None
    } else syntacticMatching( a, b )

  def Subst( subProof: ResolutionProof, substitution: Substitution ): ResolutionProof =
    subProof match {
      case _ if substitution.isIdentity => subProof
      case Subst( subProof2, substitution2 ) =>
        Subst( subProof2, substitution compose substitution2 )
      case _ => gapt.proofs.resolution.Subst( subProof, substitution )
    }

  object Clausification extends Clausifier(
    propositional,
    structural = true,
    bidirectionalDefs = false,
    cse = false,
    ctx = state.ctx,
    nameGen = state.nameGen ) with InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
      if ( given.clause.forall( _.isInstanceOf[Atom] ) ) ( Set(), Set() )
      else {
        expand( given.proof )

        val consts = constants( cnf.map( _.conclusion.elements ).flatMap( constants( _ ) ).
          filter( _.name != "=" ) ).map( _.name )
        state.termOrdering match {
          case LPO( precedence, typeOrder ) =>
            val pc = precedence.takeWhile( state.ctx.constant( _ ).exists( arity( _ ) == 0 ) )
            state.termOrdering = LPO( pc ++ consts.diff( precedence.toSet ) ++ precedence.drop( pc.size ), typeOrder )
        }

        val inferred = cnf.map( SimpCls( given, _ ) ).toSet
        cnf.clear()
        ( inferred, Set( given -> Set() ) )
      }
  }

  object TautologyDeletion extends RedundancyRule {
    def isRedundant( given: Cls, existing: Set[Cls] ): Option[Set[Int]] =
      if ( given.clause.isTaut || given.assertion.isTaut ) Some( Set() ) else None
  }

  object EqualityResolution extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[( Cls, Set[Int] )] = {
      val refls = given.clause.antecedent collect { case Eq( t, t_ ) if t == t_ => t }
      if ( refls.isEmpty ) None
      else Some( SimpCls( given, refls.foldRight( given.proof )( ( t, proof ) =>
        Resolution( Refl( t ), Suc( 0 ), proof, proof.conclusion.indexOfInAnt( t === t ) ) ) ) -> Set() )
    }
  }

  object ReflexivityDeletion extends RedundancyRule {
    def isRedundant( given: Cls, existing: Set[Cls] ): Option[Set[Int]] =
      if ( given.clause.succedent exists {
        case Eq( t, t_ ) if t == t_ => true
        case _                      => false
      } ) Some( Set() ) else None
  }

  object OrderEquations extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[( Cls, Set[Int] )] = {
      val toFlip = given.clause filter {
        case Eq( t, s ) => termOrdering.lt( s, t )
        case _          => false
      }
      if ( toFlip.isEmpty ) {
        None
      } else {
        var p = given.proof
        for ( e <- toFlip ) p = Flip( p, p.conclusion indexOf e )
        Some( SimpCls( given, p ) -> Set() )
      }
    }
  }

  object ClauseFactoring extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[( Cls, Set[Int] )] =
      if ( given.clause == given.clause.distinct ) None
      else Some( SimpCls( given, Factor( given.proof ) ) -> Set() )
  }

  object DuplicateDeletion extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls] =
      newlyInferred.groupBy( _.clauseWithAssertions ).values.map( _.head ).toSet
  }

  object ReflModEqDeletion extends RedundancyRule {

    def canonize( expr: Expr, assertion: HOLClause, existing: Set[Cls] ): Expr = {
      val eqs = for {
        c <- existing
        if c.assertion isSubMultisetOf assertion
        Sequent( Seq(), Seq( Eq( t, s ) ) ) <- choose( c.clause )
        if matching( t, s ).isDefined
        if matching( s, t ).isDefined
        ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) )
        if !termOrdering.lt( t_, s_ )
      } yield ( t_, s_, c, leftToRight )
      if ( eqs isEmpty ) return expr

      var e = expr
      var didRewrite = true
      while ( didRewrite ) {
        didRewrite = false
        for {
          ( subterm, pos ) <- getFOPositions( e ) if !didRewrite
          if !subterm.isInstanceOf[Var]
          ( t_, s_, c1, leftToRight ) <- eqs if !didRewrite
          subst <- matching( t_, subterm )
          if termOrdering.lt( subst( s_ ), subterm, treatVarsAsConsts = true )
        } {
          for ( p <- pos ) e = e.replace( p, subst( s_ ) )
          didRewrite = true
        }
      }
      e
    }

    def isRedundant( given: Cls, existing: Set[Cls] ): Option[Set[Int]] =
      if ( given.clause.succedent exists {
        case Eq( t, s ) => canonize( t, given.assertion, existing ) == canonize( s, given.assertion, existing )
        case _          => false
      } ) Some( Set() ) else None

  }

  object SubsumptionInterreduction extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls] = {
      val interreduced = newlyInferred.to[mutable.Set]
      for {
        cls1 <- interreduced
        cls2 <- interreduced if cls1 != cls2
        if interreduced contains cls1
        if cls2.ass subsetOf cls1.ass
        _ <- subsume( cls2, cls1 )
      } interreduced -= cls1
      interreduced.toSet
    }
  }

  object ForwardSubsumption extends RedundancyRule {
    def isRedundant( given: Cls, existing: Set[Cls] ): Option[Set[Int]] =
      existing.view.collectFirst { case e if subsume( e, given ).isDefined => e.ass }
  }

  object BackwardSubsumption extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
      ( Set(), existing.collect { case e if subsume( given, e ).isDefined => e -> given.ass } )
  }

  def choose[T]( ts: T* ): Seq[T] = ts

  object ForwardUnitRewriting extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[( Cls, Set[Int] )] = {
      val eqs = for {
        c <- existing
        if c.ass subsetOf given.ass // FIXME
        Sequent( Seq(), Seq( Eq( t, s ) ) ) <- choose( c.clause )
        ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) )
        if !t_.isInstanceOf[Var]
        if !termOrdering.lt( t_, s_ )
      } yield ( t_, s_, c, leftToRight )
      if ( eqs isEmpty ) return None

      var p = given.proof
      var didRewrite = true
      var reason = Set[Int]()
      while ( didRewrite ) {
        didRewrite = false
        for {
          i <- p.conclusion.indices if !didRewrite
          ( subterm, pos ) <- getFOPositions( p.conclusion( i ) ) if !didRewrite
          if !subterm.isInstanceOf[Var]
          ( t_, s_, c1, leftToRight ) <- eqs if !didRewrite
          subst <- matching( t_, subterm )
          if termOrdering.lt( subst( s_ ), subterm )
        } {
          p = Paramod( Subst( c1.proof, subst ), Suc( 0 ), leftToRight,
            p, i, replacementContext( subst( t_.ty ), p.conclusion( i ), pos ) )
          reason = reason ++ c1.ass
          didRewrite = true
        }
      }

      if ( p != given.proof ) {
        Some( SimpCls( given, p ) -> reason )
      } else {
        None
      }
    }
  }

  object BackwardUnitRewriting extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred = mutable.Set[Cls]()
      val deleted = mutable.Set[( Cls, Set[Int] )]()

      for ( e <- existing ) {
        val ( i, d ) = ForwardUnitRewriting( e, Set( given ) )
        inferred ++= i
        deleted ++= d
      }

      ( inferred.toSet, deleted.toSet )
    }
  }

  object OrderedResolution extends BinaryInferenceRule {
    def apply( c1: Cls, c2: Cls ): Set[Cls] = {
      if ( c2.selected.nonEmpty ) return Set()
      val renaming = Substitution( rename( c2.freeVars, c1.freeVars ) )
      val p2_ = Subst( c2.proof, renaming )
      val inferred = for {
        i1 <- if ( c1.selected.nonEmpty ) c1.selected else c1.maximal
        a1 = c1.clause( i1 ) if i1 isAnt;
        i2 <- c2.maximal if i2 isSuc;
        mgu <- unify( p2_.conclusion( i2 ), a1 )
        if c1.selected.nonEmpty || !c1.maximal.exists { i1_ => i1_ != i1 && termOrdering.lt( a1, mgu( c1.clause( i1_ ) ) ) }
        if !c2.maximal.exists { i2_ => i2_ != i2 && termOrdering.lt( mgu( p2_.conclusion( i2 ) ), mgu( p2_.conclusion( i2_ ) ) ) }
        ( p1__, conn1 ) = Factor.withOccConn( Subst( c1.proof, mgu ) )
        ( p2__, conn2 ) = Factor.withOccConn( Subst( p2_, mgu ) )
      } yield DerivedCls( c1, c2, Resolution( p2__, conn2 child i2, p1__, conn1 child i1 ) )
      inferred.toSet
    }
  }

  object Superposition extends BinaryInferenceRule {
    def isReductive( atom: Formula, i: SequentIndex, pos: LambdaPosition ): Boolean =
      ( atom, i, pos.toList ) match {
        case ( Eq( t, s ), _: Suc, 2 :: _ )      => !termOrdering.lt( s, t )
        case ( Eq( t, s ), _: Suc, 1 :: 2 :: _ ) => !termOrdering.lt( t, s )
        case _                                   => true
      }

    def apply( c1: Cls, c2: Cls ): Set[Cls] = {
      if ( c1.selected.nonEmpty ) return Set()
      val renaming = Substitution( rename( c2.freeVars, c1.freeVars ) )
      val p2_ = Subst( c2.proof, renaming )

      val inferred = for {
        i1 <- c1.maximal; Eq( t, s ) <- choose( c1.clause( i1 ) ) if i1.isSuc
        ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) ) if !termOrdering.lt( t_, s_ )
        i2 <- if ( c2.selected.nonEmpty ) c2.selected else c2.maximal
        a2 = p2_.conclusion( i2 )
        ( st2, pos2 ) <- getFOPositions( a2 )
        if !st2.isInstanceOf[Var]
        mgu <- unify( t_, st2 )
        if !termOrdering.lt( mgu( t_ ), mgu( s_ ) )
        pos2_ = pos2 filter { isReductive( mgu( a2 ), i2, _ ) } if pos2_.nonEmpty
        p1__ = Subst( c1.proof, mgu )
        p2__ = Subst( p2_, mgu )
        ( equation, atom ) = ( p1__.conclusion( i1 ), p2__.conclusion( i2 ) )
        context = replacementContext( s.ty, atom, pos2_ )
      } yield DerivedCls( c1, c2, Paramod( p1__, i1, leftToRight, p2__, i2, context ) )

      inferred.toSet
    }
  }

  object Factoring extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred =
        for {
          i <- given.maximal; j <- given.maximal
          if i < j && i.sameSideAs( j )
          mgu <- unify( given.clause( i ), given.clause( j ) )
        } yield DerivedCls( given, Subst( given.proof, mgu ) )
      ( inferred.toSet, Set() )
    }
  }

  object UnifyingEqualityResolution extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred =
        for {
          i <- if ( given.selected.nonEmpty ) given.selected else given.maximal if i.isAnt
          Eq( t, s ) <- Some( given.clause( i ) )
          mgu <- unify( t, s )
        } yield DerivedCls( given, Subst( given.proof, mgu ) )
      ( inferred.toSet, Set() )
    }
  }

  object AvatarSplitting extends InferenceRule {

    var componentCache = mutable.Map[Formula, Atom]()
    def boxComponent( comp: HOLSequent ): AvatarNonGroundComp = {
      val definition @ All.Block( vs, _ ) = universalClosure( comp.toDisjunction )
      AvatarNonGroundComp(
        componentCache.getOrElseUpdate( definition, {
          val tvs = typeVariables( definition ).toList
          val c = Const( nameGen.freshWithIndex( "split" ), To, tvs )
          state.ctx += Definition( c, definition )
          c.asInstanceOf[Atom]
        } ), definition, vs )
    }

    val componentAlreadyDefined = mutable.Set[Atom]()
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val comps = AvatarSplit.getComponents( given.clause )

      if ( comps.size >= 2 ) {
        val propComps = comps.filter( freeVariables( _ ).isEmpty ).map {
          case Sequent( Seq( a: Atom ), Seq() ) => AvatarGroundComp( a, Polarity.InAntecedent )
          case Sequent( Seq(), Seq( a: Atom ) ) => AvatarGroundComp( a, Polarity.InSuccedent )
        }
        val nonPropComps =
          for ( c <- comps if freeVariables( c ).nonEmpty )
            yield boxComponent( c )

        val split = AvatarSplit( given.proof, nonPropComps ++ propComps )
        var inferred = Set( DerivedCls( given, split ) )
        for ( comp <- propComps; if !componentAlreadyDefined( comp.atom ) ) {
          componentAlreadyDefined += comp.atom
          for ( pol <- Polarity.values )
            inferred += DerivedCls( given, AvatarComponent( AvatarGroundComp( comp.atom, pol ) ) )
        }
        for ( comp <- nonPropComps if !componentAlreadyDefined( comp.atom ) ) {
          componentAlreadyDefined += comp.atom
          inferred += DerivedCls( given, AvatarComponent( comp ) )
        }

        ( inferred, Set( given -> Set() ) )
      } else {
        ( Set(), Set() )
      }
    }

  }

}