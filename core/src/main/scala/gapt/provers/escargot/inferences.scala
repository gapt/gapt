package gapt.provers.escargot.impl

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Atom
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.universalClosure
import gapt.expr.subst.Substitution
import gapt.expr.ty.To
import gapt.expr.ty.arity
import gapt.expr.util.LambdaPosition
import gapt.expr.util.LambdaPosition.Choice
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.expr.util.replacementContext
import gapt.expr.util.syntacticMGU
import gapt.expr.util.syntacticMatching
import gapt.expr.util.typeVariables
import gapt.logic.Polarity
import gapt.logic.clauseSubsumption
import gapt.proofs._
import gapt.proofs.context.update.Definition
import gapt.proofs.resolution._
import gapt.provers.escargot.LPO

import scala.collection.mutable

trait PreprocessingRule {
  def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls]
}

/**
 * An operation that looks at the given clause, and the set of worked off clauses;
 * it returns a set of new clauses, plus a set of clauses that should be discarded.
 */
trait InferenceRule extends PreprocessingRule {
  def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] )

  def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls] = {
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

trait RedundancyRule extends InferenceRule {
  def isRedundant( `given`: Cls, existing: IndexedClsSet ): Option[Set[Int]]
  def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    isRedundant( given, existing ) match {
      case Some( reason ) => ( Set(), Set( given -> reason ) )
      case None           => ( Set(), Set() )
    }
}

trait SimplificationRule extends InferenceRule {
  def simplify( `given`: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )]
  def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
    simplify( given, existing ) match {
      case Some( ( simplified, reason ) ) => ( Set( simplified ), Set( given -> reason ) )
      case None                           => ( Set(), Set() )
    }
}

object getFOPositions {
  def apply( exp: Expr ): Map[Expr, Seq[LambdaPosition]] = {
    val poss = mutable.Map[Expr, Seq[LambdaPosition]]().withDefaultValue( Seq() )
    def walk( exp: Expr, pos: List[Choice] ): Unit = {
      poss( exp ) :+= LambdaPosition( pos.reverse: _* )
      walkApp( exp, pos )
    }
    def walkApp( exp: Expr, pos: List[Choice] ): Unit = exp match {
      case App( f, arg ) =>
        walk( arg, LambdaPosition.Right :: pos )
        walkApp( f, LambdaPosition.Left :: pos )
      case _ =>
    }
    walk( exp, Nil )
    poss.toMap
  }
}

object UnitRwrLhsIndex extends Index[DiscrTree[( Expr, Expr, Boolean, Cls )]] {
  def empty: I = DiscrTree()
  private def choose[T]( ts: T* ): Seq[T] = ts
  def add( t: I, c: Cls ): I =
    t.insert( c.clause match {
      case Sequent( Seq(), Seq( Eq( t, s ) ) ) =>
        for {
          ( t_, s_, ltr ) <- choose( ( t, s, true ), ( s, t, false ) )
          if !t_.isInstanceOf[Var]
          if !c.state.termOrdering.lt( t_, s_ )
        } yield t_ -> ( t_, s_, ltr, c )
      case _ => Seq.empty
    } )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._4 ) )
}

object MaxPosLitIndex extends Index[DiscrTree[( Cls, SequentIndex )]] {
  def empty: I = DiscrTree()
  def add( t: I, c: Cls ): I =
    t.insert( for ( i <- c.maximal if i.isSuc if c.selected.isEmpty )
      yield c.clause( i ) -> ( c, i ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

object SelectedLitIndex extends Index[DiscrTree[( Cls, SequentIndex )]] {
  def empty: I = DiscrTree()
  def add( t: I, c: Cls ): I =
    t.insert( for {
      i <- if ( c.selected.nonEmpty ) c.selected else c.maximal
      if i.isAnt
    } yield c.clause( i ) -> ( c, i ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

object ForwardSuperpositionIndex extends Index[DiscrTree[( Cls, SequentIndex, Expr, Expr, Boolean )]] {
  def empty: I = DiscrTree()
  private def choose[T]( ts: T* ): Seq[T] = ts
  def add( t: I, c: Cls ): I =
    t.insert( for {
      i <- c.maximal if i.isSuc if c.selected.isEmpty
      Eq( t, s ) <- choose( c.clause( i ) )
      ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) )
      if !c.state.termOrdering.lt( t_, s_ )
    } yield t_ -> ( c, i, t_, s_, leftToRight ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
}

object BackwardSuperpositionIndex extends Index[DiscrTree[( Cls, SequentIndex, Expr, Seq[LambdaPosition] )]] {
  def empty: I = DiscrTree()
  def add( t: I, c: Cls ): I =
    t.insert( for {
      i <- if ( c.selected.nonEmpty ) c.selected else c.maximal
      a = c.clause( i )
      ( st, pos ) <- getFOPositions( a )
      if !st.isInstanceOf[Var]
    } yield st -> ( c, i, st, pos ) )
  def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._1 ) )
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
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
      if ( given.clause.forall( _.isInstanceOf[Atom] ) ) ( Set(), Set() )
      else {
        expand( given.proof )

        val consts = constants.nonLogical( cnf.map( _.conclusion.elements ).flatMap( constants.nonLogical( _ ) ).
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
    def isRedundant( `given`: Cls, existing: IndexedClsSet ): Option[Set[Int]] =
      if ( given.clause.isTaut || given.assertion.isTaut ) Some( Set() ) else None
  }

  object EqualityResolution extends SimplificationRule {
    def simplify( `given`: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val refls = given.clause.antecedent collect { case Eq( t, t_ ) if t == t_ => t }
      if ( refls.isEmpty ) None
      else Some( SimpCls( given, refls.foldRight( given.proof )( ( t, proof ) =>
        Resolution( Refl( t ), Suc( 0 ), proof, proof.conclusion.indexOfInAnt( t === t ) ) ) ) -> Set() )
    }
  }

  object ReflexivityDeletion extends RedundancyRule {
    def isRedundant( `given`: Cls, existing: IndexedClsSet ): Option[Set[Int]] =
      if ( given.clause.succedent exists {
        case Eq( t, t_ ) if t == t_ => true
        case _                      => false
      } ) Some( Set() ) else None
  }

  object OrderEquations extends SimplificationRule {
    def simplify( `given`: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
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
    def simplify( `given`: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] =
      if ( given.clause == given.clause.distinct ) None
      else Some( SimpCls( given, Factor( given.proof ) ) -> Set() )
  }

  object DuplicateDeletion extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls] =
      newlyInferred.groupBy( _.clauseWithAssertions ).values.map( _.head ).toSet
  }

  object ReflModEqIndex extends Index[DiscrTree[( Expr, Expr, Boolean, Cls )]] {
    def empty: I = DiscrTree()
    private def choose[T]( ts: T* ): Seq[T] = ts
    def add( t: I, c: Cls ): I =
      t.insert( c.clause match {
        case Sequent( Seq(), Seq( Eq( t, s ) ) ) if matching( t, s ).isDefined
          && matching( s, t ).isDefined =>
          for {
            ( t_, s_, leftToRight ) <- choose( ( t, s, true ), ( s, t, false ) )
            if !termOrdering.lt( t_, s_ )
            if !t_.isInstanceOf[Var]
          } yield t_ -> ( t_, s_, leftToRight, c )
        case _ => Seq.empty
      } )
    def remove( t: I, cs: Set[Cls] ): I = t.filter( e => !cs( e._4 ) )
  }

  object ReflModEqDeletion extends RedundancyRule {

    def canonize( expr: Expr, assertion: Set[Int], eqs: ReflModEqIndex.I ): Expr = {
      var e = expr
      var didRewrite = true
      while ( didRewrite ) {
        didRewrite = false
        for {
          ( subterm, pos ) <- getFOPositions( e ) if !didRewrite
          if !subterm.isInstanceOf[Var]
          ( t_, s_, _, c1 ) <- eqs.generalizations( subterm ) if !didRewrite
          if c1.ass subsetOf assertion
          subst <- matching( t_, subterm )
          if termOrdering.lt( subst( s_ ), subterm, treatVarsAsConsts = true )
        } {
          for ( p <- pos ) e = e.replace( p, subst( s_ ) )
          didRewrite = true
        }
      }
      e
    }

    def isRedundant( `given`: Cls, existing: IndexedClsSet ): Option[Set[Int]] = {
      val eqs = existing.getIndex( ReflModEqIndex )
      if ( !eqs.isEmpty && given.clause.succedent.exists {
        case Eq( t, s ) => canonize( t, given.ass, eqs ) == canonize( s, given.ass, eqs )
        case _          => false
      } ) Some( Set() ) else None
    }

  }

  object SubsumptionInterreduction extends PreprocessingRule {
    def preprocess( newlyInferred: Set[Cls], existing: IndexedClsSet ): Set[Cls] = {
      val interreduced = newlyInferred.to( mutable.Set )
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
    def isRedundant( `given`: Cls, existing: IndexedClsSet ): Option[Set[Int]] =
      existing.clauses.collectFirst { case e if subsume( e, given ).isDefined => e.ass }
  }

  object BackwardSubsumption extends InferenceRule {
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) =
      ( Set(), existing.clauses.collect { case e if subsume( given, e ).isDefined => e -> given.ass } )
  }

  def choose[T]( ts: T* ): Seq[T] = ts

  object ForwardUnitRewriting extends SimplificationRule {
    def simplify( `given`: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val unitRwrLhs = existing.getIndex( UnitRwrLhsIndex )
      if ( unitRwrLhs.isEmpty ) return None

      var p = given.proof
      var didRewrite = true
      var reason = Set[Int]()
      while ( didRewrite ) {
        didRewrite = false
        for {
          i <- p.conclusion.indices if !didRewrite
          ( subterm, pos ) <- getFOPositions( p.conclusion( i ) ) if !didRewrite
          if !subterm.isInstanceOf[Var]
          ( t_, s_, leftToRight, c1 ) <- unitRwrLhs.generalizations( subterm ) if !didRewrite
          if c1.ass subsetOf given.ass // FIXME: large performance difference? e.g. ALG200+1
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
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred = mutable.Set[Cls]()
      val deleted = mutable.Set[( Cls, Set[Int] )]()

      val givenSet = IndexedClsSet( state ).addIndex( UnitRwrLhsIndex ) + given
      for ( e <- existing.clauses ) {
        val ( i, d ) = ForwardUnitRewriting( e, givenSet )
        inferred ++= i
        deleted ++= d
      }

      ( inferred.toSet, deleted.toSet )
    }
  }

  object OrderedResolution extends InferenceRule {
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val givenSet = IndexedClsSet( state ).addIndex( SelectedLitIndex ).addIndex( MaxPosLitIndex ) + given
      val existingPlusGiven = existing + given
      val inferred1 =
        for {
          ( c1, i1 ) <- givenSet.getIndex( SelectedLitIndex ).elements
          ( c2, i2 ) <- existingPlusGiven.getIndex( MaxPosLitIndex ).unifiable( c1.clause( i1 ) )
          cn <- apply( c1, i1, c2, i2 )
        } yield cn
      val inferred2 =
        for {
          ( c2, i2 ) <- givenSet.getIndex( MaxPosLitIndex ).elements
          ( c1, i1 ) <- existing.getIndex( SelectedLitIndex ).unifiable( c2.clause( i2 ) )
          cn <- apply( c1, i1, c2, i2 )
        } yield cn

      ( Set() ++ inferred1 ++ inferred2, Set() )
    }

    // i1.isAnt i2.isSuc
    def apply( c1: Cls, i1: SequentIndex, c2: Cls, i2: SequentIndex ): Option[Cls] = {
      val renaming = Substitution( rename( c2.freeVars, c1.freeVars ) )
      val p2_ = Subst( c2.proof, renaming )
      val a1 = c1.clause( i1 )
      for {
        mgu <- unify( p2_.conclusion( i2 ), a1 )
        if c1.selected.nonEmpty || !c1.maximal.exists { i1_ => i1_ != i1 && termOrdering.lt( mgu( a1 ), mgu( c1.clause( i1_ ) ) ) }
        if !c2.maximal.exists { i2_ => i2_ != i2 && termOrdering.lt( mgu( p2_.conclusion( i2 ) ), mgu( p2_.conclusion( i2_ ) ) ) }
        ( p1__, conn1 ) = Factor.withOccConn( Subst( c1.proof, mgu ) )
        ( p2__, conn2 ) = Factor.withOccConn( Subst( p2_, mgu ) )
      } yield DerivedCls( c1, c2, Resolution( p2__, conn2 child i2, p1__, conn1 child i1 ) )
    }
  }

  object Superposition extends InferenceRule {
    def isReductive( atom: Formula, i: SequentIndex, pos: LambdaPosition ): Boolean =
      ( atom, i, pos.toList ) match {
        case ( Eq( t, s ), _: Suc, LambdaPosition.Right :: _ ) => !termOrdering.lt( s, t )
        case ( Eq( t, s ), _: Suc, LambdaPosition.Left :: LambdaPosition.Right :: _ ) => !termOrdering.lt( t, s )
        case _ => true
      }

    def eligible( c: Cls, c1: HOLSequent, mgu: Substitution, i: SequentIndex ): Boolean = {
      val a = mgu( c1( i ) )
      def maximalIn( is: Iterable[SequentIndex] ): Boolean =
        !is.exists( i_ => i_ != i && termOrdering.lt( a, mgu( c1( i_ ) ) ) )
      if ( c.selected.isEmpty ) maximalIn( c.maximal )
      else maximalIn( c.selected.view.filter( _.isAnt ) ) || maximalIn( c.selected.view.filter( _.isSuc ) )
    }

    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val givenSet = IndexedClsSet( state ).
        addIndex( ForwardSuperpositionIndex ).
        addIndex( BackwardSuperpositionIndex ) +
        given
      val existingPlusGiven = existing + given
      val inferred1 =
        for {
          ( c1, i1, t1, s1, ltr ) <- givenSet.getIndex( ForwardSuperpositionIndex ).elements
          ( c2, i2, _, pos2 ) <- existingPlusGiven.getIndex( BackwardSuperpositionIndex ).unifiable( t1 )
          cn <- apply( c1, i1, t1, s1, ltr, c2, i2, pos2 )
        } yield cn
      val inferred2 =
        for {
          ( c2, i2, st2, pos2 ) <- givenSet.getIndex( BackwardSuperpositionIndex ).elements
          ( c1, i1, t1, s1, ltr ) <- existing.getIndex( ForwardSuperpositionIndex ).unifiable( st2 )
          cn <- apply( c1, i1, t1, s1, ltr, c2, i2, pos2 )
        } yield cn

      ( Set() ++ inferred1 ++ inferred2, Set() )
    }

    // i1.isSuc, c1.clause(i1) == Eq(_, _)
    def apply( c1: Cls, i1: SequentIndex, t_ : Expr, s_ : Expr, leftToRight: Boolean,
               c2: Cls, i2: SequentIndex, pos2: Seq[LambdaPosition] ): Option[Cls] = {
      val renaming = Substitution( rename( c2.freeVars, c1.freeVars ) )
      val p2_ = Subst( c2.proof, renaming )
      val a2 = p2_.conclusion( i2 )
      val st2 = a2( pos2.head )
      for {
        mgu <- unify( t_, st2 )
        if !termOrdering.lt( mgu( t_ ), mgu( s_ ) )
        pos2_ = pos2.filter( isReductive( mgu( a2 ), i2, _ ) ) if pos2_.nonEmpty
        if eligible( c2, p2_.conclusion, mgu, i2 )
        p1__ = Subst( c1.proof, mgu )
        p2__ = Subst( p2_, mgu )
        atom = p2__.conclusion( i2 )
        context = replacementContext( mgu( s_.ty ), atom, pos2_ )
      } yield DerivedCls( c1, c2, Paramod( p1__, i1, leftToRight, p2__, i2, context ) )
    }
  }

  object Factoring extends InferenceRule {
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
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
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
      val inferred =
        for {
          i <- if ( given.selected.nonEmpty ) given.selected else given.maximal if i.isAnt
          Eq( t, s ) <- Some( given.clause( i ) )
          mgu <- unify( t, s )
        } yield DerivedCls( given, Subst( given.proof, mgu ) )
      ( inferred.toSet, Set() )
    }
  }

  object VariableEqualityResolution extends SimplificationRule {
    def simp( p: ResolutionProof ): ResolutionProof =
      p.conclusion.antecedent.zipWithIndex.collectFirst {
        case ( Eq( x: Var, t ), i ) if !freeVariables( t ).contains( x ) => ( x, t, i )
        case ( Eq( t, x: Var ), i ) if !freeVariables( t ).contains( x ) => ( x, t, i )
      } match {
        case Some( ( x, t, i ) ) =>
          simp( Resolution( Refl( t ), Suc( 0 ), Subst( p, Substitution( x -> t ) ), Ant( i ) ) )
        case None => p
      }

    override def simplify( `given`: Cls, existing: IndexedClsSet ): Option[( Cls, Set[Int] )] = {
      val q = simp( given.proof )
      if ( q eq given.proof ) None else Some( SimpCls( given, q ) -> Set.empty )
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
    def apply( `given`: Cls, existing: IndexedClsSet ): ( Set[Cls], Set[( Cls, Set[Int] )] ) = {
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
