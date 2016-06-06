package at.logic.gapt.provers.escargot.impl

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution._

import scala.collection.mutable

trait PreprocessingRule {
  def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls]
}

trait InferenceRule extends PreprocessingRule {
  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] )

  def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls] = {
    val inferred = mutable.Set[Cls]()
    val deleted = mutable.Set[Cls]()

    for ( c <- newlyInferred ) {
      val ( i, d ) = apply( c, existing )
      inferred ++= i
      deleted ++= d
    }

    newlyInferred -- deleted ++ inferred
  }
}

trait BinaryInferenceRule extends InferenceRule {
  def apply( a: Cls, b: Cls ): Set[Cls]

  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) =
    ( existing.flatMap( apply( given, _ ) ) ++
      existing.flatMap( apply( _, given ) ) ++
      apply( given, given ),
      Set() )
}

trait RedundancyRule extends InferenceRule {
  def isRedundant( given: Cls, existing: Set[Cls] ): Boolean
  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) =
    if ( isRedundant( given, existing ) ) ( Set(), Set( given ) )
    else ( Set(), Set() )
}

trait SimplificationRule extends InferenceRule {
  def simplify( given: Cls, existing: Set[Cls] ): Option[Cls]
  def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) =
    simplify( given, existing ) match {
      case Some( simplified ) => ( Set( simplified ), Set( given ) )
      case None               => ( Set(), Set() )
    }
}

class StandardInferences( state: EscargotState, propositional: Boolean ) {
  import state.{ DerivedCls, SimpCls, termOrdering, nameGen }

  def subsume( a: Cls, b: Cls ): Option[Substitution] =
    if ( a.assertion isSubsetOf b.assertion ) subsume( a.clause, b.clause )
    else None
  def subsume( a: HOLClause, b: HOLClause ): Option[Substitution] =
    if ( propositional ) {
      if ( a isSubMultisetOf b ) Some( Substitution() )
      else None
    } else clauseSubsumption( a, b, multisetSubsumption = true )
  def unify( a: LambdaExpression, b: LambdaExpression ): Option[Substitution] =
    if ( propositional ) {
      if ( a == b ) Some( Substitution() )
      else None
    } else syntacticMGU( a, b )
  def matching( a: LambdaExpression, b: LambdaExpression ): Option[Substitution] =
    if ( propositional ) {
      if ( a == b ) Some( Substitution() )
      else None
    } else syntacticMatching( a, b )

  def Subst( proof: ResolutionProof, subst: Substitution ) =
    if ( subst( proof.conclusion ) == proof.conclusion ) proof
    else at.logic.gapt.proofs.resolution.Subst( proof, subst )

  object TautologyDeletion extends RedundancyRule {
    def isRedundant( given: Cls, existing: Set[Cls] ): Boolean =
      given.clause.isTaut || given.assertion.isTaut
  }

  object EqualityResolution extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[Cls] = {
      val refls = given.clause.antecedent collect { case Eq( t, t_ ) if t == t_ => t }
      if ( refls.isEmpty ) None
      else Some( SimpCls( given, refls.foldRight( given.proof )( ( t, proof ) =>
        Resolution( Refl( t ), Suc( 0 ), proof, proof.conclusion.indexOfInAnt( t === t ) ) ) ) )
    }
  }

  object ReflexivityDeletion extends RedundancyRule {
    def isRedundant( given: Cls, existing: Set[Cls] ): Boolean =
      given.clause.succedent exists {
        case Eq( t, t_ ) if t == t_ => true
        case _                      => false
      }
  }

  object OrderEquations extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[Cls] = {
      val toFlip = given.clause filter {
        case Eq( t, s ) => termOrdering.lt( s, t )
        case _          => false
      }
      if ( toFlip.isEmpty ) {
        None
      } else {
        var p = given.proof
        for ( e <- toFlip ) p = Flip( p, p.conclusion indexOf e )
        Some( SimpCls( given, p ) )
      }
    }
  }

  object ClauseFactoring extends SimplificationRule {
    def simplify( given: Cls, existing: Set[Cls] ): Option[Cls] =
      if ( given.clause == given.clause.distinct ) None
      else Some( SimpCls( given, Factor( given.proof ) ) )
  }

  object DuplicateDeletion extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls] =
      newlyInferred.groupBy( _.clauseWithAssertions ).values.map( _.head ).toSet
  }

  object ReflModEqDeletion extends RedundancyRule {

    def canonize( expr: LambdaExpression, assertion: HOLClause, existing: Set[Cls] ): LambdaExpression = {
      val eqs = for {
        c <- existing
        if c.assertion isSubsetOf assertion
        Sequent( Seq(), Seq( Eq( t, s ) ) ) <- Seq( c.clause )
        if matching( t, s ).isDefined
        if matching( s, t ).isDefined
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
          subst <- matching( t_, subterm )
          if termOrdering.lt( subst( s_ ), subterm, treatVarsAsConsts = true )
        } {
          for ( p <- pos ) e = e.replace( p, subst( s_ ) )
          didRewrite = true
        }
      }
      e
    }

    def isRedundant( given: Cls, existing: Set[Cls] ): Boolean =
      given.clause.succedent exists {
        case Eq( t, s ) => canonize( t, given.assertion, existing ) == canonize( s, given.assertion, existing )
        case _          => false
      }

  }

  object SubsumptionInterreduction extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: Set[Cls] ): Set[Cls] = {
      val interreduced = newlyInferred.to[mutable.Set]
      for {
        cls1 <- interreduced
        cls2 <- interreduced if cls1 != cls2
        if interreduced contains cls1
        _ <- subsume( cls2, cls1 )
      } interreduced -= cls1
      interreduced.toSet
    }
  }

  object ForwardSubsumption extends RedundancyRule {
    def isRedundant( given: Cls, existing: Set[Cls] ): Boolean =
      existing exists { subsume( _, given ).isDefined }
  }

  object BackwardSubsumption extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) =
      ( Set(), existing filter { subsume( given, _ ).isDefined } )
  }

  object ForwardUnitRewriting extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) = {
      val eqs = for {
        c <- existing
        Sequent( Seq(), Seq( Eq( t, s ) ) ) <- Seq( c.clause )
        if c.assertion isSubsetOf given.assertion
        ( t_, s_, leftToRight ) <- Seq( ( t, s, true ), ( s, t, false ) )
        if !t_.isInstanceOf[Var]
        if !termOrdering.lt( t_, s_ )
      } yield ( t_, s_, c, leftToRight )
      if ( eqs isEmpty ) return ( Set(), Set() )

      var p = given.proof
      var didRewrite = true
      while ( didRewrite ) {
        didRewrite = false
        for {
          i <- p.conclusion.indices if !didRewrite
          ( subterm, pos ) <- LambdaPosition getPositions p.conclusion( i ) groupBy { p.conclusion( i )( _ ) } if !didRewrite
          if !subterm.isInstanceOf[Var]
          ( t_, s_, c1, leftToRight ) <- eqs if !didRewrite
          subst <- matching( t_, subterm )
          if termOrdering.lt( subst( s_ ), subterm )
        } {
          p = Paramod( Subst( c1.proof, subst ), Suc( 0 ), leftToRight,
            p, i, replacementContext( t_.exptype, p.conclusion( i ), pos ) )
          didRewrite = true
        }
      }

      if ( p != given.proof ) {
        ( Set( SimpCls( given, p ) ), Set( given ) )
      } else {
        ( Set(), Set() )
      }
    }
  }

  object BackwardUnitRewriting extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) = {
      val inferred = mutable.Set[Cls]()
      val deleted = mutable.Set[Cls]()

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
      val renaming = Substitution( rename( freeVariables( c2.clause ), freeVariables( c1.clause ) ) )
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
    def isReductive( atom: HOLFormula, i: SequentIndex, pos: LambdaPosition ): Boolean =
      ( atom, i, pos.toList ) match {
        case ( Eq( t, s ), _: Suc, 2 :: _ )      => !termOrdering.lt( s, t )
        case ( Eq( t, s ), _: Suc, 1 :: 2 :: _ ) => !termOrdering.lt( t, s )
        case _                                   => true
      }

    def apply( c1: Cls, c2: Cls ): Set[Cls] = {
      if ( c1.selected.nonEmpty ) return Set()
      val renaming = Substitution( rename( freeVariables( c2.clause ), freeVariables( c1.clause ) ) )
      val p2_ = Subst( c2.proof, renaming )

      val inferred = for {
        i1 <- c1.maximal; Eq( t, s ) <- Seq( c1.clause( i1 ) ) if i1.isSuc
        ( t_, s_, leftToRight ) <- Seq( ( t, s, true ), ( s, t, false ) ) if !termOrdering.lt( t_, s_ )
        i2 <- if ( c2.selected.nonEmpty ) c2.selected else c2.maximal
        a2 = p2_.conclusion( i2 )
        ( st2, pos2 ) <- LambdaPosition getPositions a2 groupBy { a2( _ ) }
        if !st2.isInstanceOf[Var]
        mgu <- unify( t_, st2 )
        if !termOrdering.lt( mgu( t_ ), mgu( s_ ) )
        pos2_ = pos2 filter { isReductive( mgu( a2 ), i2, _ ) } if pos2_.nonEmpty
        p1__ = Subst( c1.proof, mgu )
        p2__ = Subst( p2_, mgu )
        ( equation, atom ) = ( p1__.conclusion( i1 ), p2__.conclusion( i2 ) )
        context = replacementContext( s.exptype, atom, pos2_.distinct, t, s )
      } yield DerivedCls( c1, c2, Paramod( p1__, i1, leftToRight, p2__, i2, context ) )

      inferred.toSet
    }
  }

  object Factoring extends InferenceRule {
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) = {
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
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) = {
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

    def getComponents( clause: HOLClause ): List[HOLClause] = {
      def findComp( c: HOLClause ): HOLClause = {
        val fvs = freeVariables( c )
        val c_ = clause.filter( freeVariables( _ ) intersect fvs nonEmpty )
        if ( c_ isSubsetOf c ) c else findComp( c ++ c_ distinct )
      }

      if ( clause.isEmpty ) {
        Nil
      } else {
        val c = findComp( clause.map( _ +: Clause(), Clause() :+ _ ).elements.head )
        c :: getComponents( clause diff c )
      }
    }

    var componentCache = mutable.Map[HOLFormula, FOLAtom]()
    def boxComponent( comp: HOLSequent ): AvatarNonGroundComp = {
      val definition @ All.Block( vs, _ ) = univclosure( comp.toDisjunction )
      AvatarNonGroundComp( componentCache.getOrElseUpdate(
        definition,
        FOLAtom( nameGen.freshWithIndex( "split" ) )
      ), definition, vs )
    }

    val componentAlreadyDefined = mutable.Set[HOLAtom]()
    def apply( given: Cls, existing: Set[Cls] ): ( Set[Cls], Set[Cls] ) = {
      val comps = getComponents( given.clause )

      if ( comps.size >= 2 ) {
        val propComps = comps.filter( freeVariables( _ ).isEmpty ).map {
          case Sequent( Seq( a ), Seq() ) => AvatarGroundComp( a, false )
          case Sequent( Seq(), Seq( a ) ) => AvatarGroundComp( a, true )
        }
        val nonPropComps =
          for ( c <- comps if freeVariables( c ).nonEmpty )
            yield boxComponent( c )

        val split = AvatarSplit( given.proof, nonPropComps ++ propComps )
        var inferred = Set( DerivedCls( given, split ) )
        for ( comp <- propComps; if !componentAlreadyDefined( comp.atom ) ) {
          componentAlreadyDefined += comp.atom
          for ( pol <- Seq( false, true ) )
            inferred += DerivedCls( given, AvatarComponentIntro( AvatarGroundComp( comp.atom, pol ) ) )
        }
        for ( comp <- nonPropComps if !componentAlreadyDefined( comp.atom ) ) {
          componentAlreadyDefined += comp.atom
          inferred += DerivedCls( given, AvatarComponentIntro( comp ) )
        }

        ( inferred, Set( given ) )
      } else {
        ( Set(), Set() )
      }
    }

  }

}