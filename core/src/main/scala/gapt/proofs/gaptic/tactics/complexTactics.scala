package gapt.proofs.gaptic.tactics

import gapt.expr._
import gapt.expr.hol.HOLPosition
import gapt.proofs._
import gapt.proofs.expansion.{ ExpansionProofToLK, deskolemizeET }
import gapt.proofs.gaptic._
import gapt.proofs.lk._
import gapt.provers.{ Prover, ResolutionProver }
import gapt.provers.escargot.Escargot
import gapt.provers.prover9.Prover9
import gapt.provers.viper.aip.AnalyticInductionProver
import gapt.provers.viper.aip.axioms._
import cats.syntax.all._
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext

/**
 * Performs backwards chaining:
 * A goal of the form `∀x (P(x) → Q(x)), Γ :- Δ, Q(t)` is replaced by the goal `∀x (P(x) → Q(x)), Γ :- Δ, P(t)`.
 *
 * @param hyp
 * @param target
 * @param substitution
 */
case class ChainTactic( hyp: String, target: TacticApplyMode = UniqueFormula, substitution: Map[Var, Expr] = Map() ) extends Tactical1[Unit] {

  def subst( map: ( Var, Expr )* ) = copy( substitution = substitution ++ map )
  def at( target: String ) = copy( target = OnLabel( target ) )

  override def apply( goal: OpenAssumption ): Tactic[Unit] = {
    findFormula( goal, OnLabel( hyp ) ).flatMap {
      case ( _, quantifiedFormula @ All.Block( hypVar, hypInner @ Imp.Block( _, hypTargetMatch ) ), _ ) =>

        def getSubst( f: Formula ): Option[Substitution] =
          syntacticMatching( List( hypTargetMatch -> f ), PreSubstitution( substitution ++ freeVariables( quantifiedFormula ).map( v => v -> v ) ) ).headOption

        // Find target index and substitution
        findFormula( goal, target ).withFilter { case ( _, f, idx ) => idx.isSuc && getSubst( f ).isDefined }.flatMap {
          case ( targetLabel, f, targetIndex ) =>
            val Some( sub ) = getSubst( f )

            // Recursively apply implication left to the left until the end of the chain is reached,
            // where the sequent is an axiom (following some contractions).
            // The right premises of the implication left rules become new sub goals,
            // but where the initial target formula is then "forgotten".
            def handleAnds( curGoal: Sequent[( String, Formula )], hypCond: Suc ): LKProof = curGoal( hypCond ) match {
              case ( existingLabel, And( lhs, rhs ) ) =>
                AndRightRule(
                  handleAnds( curGoal.updated( hypCond, existingLabel -> lhs ), hypCond ),
                  handleAnds( curGoal.updated( hypCond, existingLabel -> rhs ), hypCond ),
                  And( lhs, rhs ) )
              case _ =>
                OpenAssumption( curGoal )
            }

            def handleImps( curGoal: Sequent[( String, Formula )], hyp: Ant ): LKProof = {
              curGoal( hyp ) match {
                case ( hypLabel, Imp( lhs, rhs ) ) =>
                  // Different methods must be applied depending on how the chain is defined.
                  val premiseLeft = handleAnds( curGoal.delete( targetIndex ).delete( hyp ) :+ ( targetLabel -> lhs ), Suc( curGoal.succedent.length - 1 ) )
                  val premiseRight = handleImps( curGoal.updated( hyp, hypLabel -> rhs ), hyp )
                  ImpLeftRule( premiseLeft, premiseRight, Imp( lhs, rhs ) )

                case ( _, formula ) =>
                  WeakeningMacroRule( LogicalAxiom( formula ), curGoal map { _._2 } )
              }
            }

            val auxFormula = sub( hypInner )
            val goalSequent = goal.labelledSequent
            val newGoal = ( NewLabel( goalSequent, hyp ) -> auxFormula ) +: goalSequent
            val premise = handleImps( newGoal, Ant( 0 ) )
            val auxProofSegment = ForallLeftBlock( premise, quantifiedFormula, sub( hypVar ) )
            replace( ContractionLeftRule( auxProofSegment, quantifiedFormula ) )
        }
    }
  }
}

/**
 * Rewrites using the specified equations at the target, either once or as often as possible.
 *
 * @param equations  Universally quantified equations on the antecedent, with direction (left-to-right?)
 * @param target  Formula to rewrite.
 * @param once  Rewrite exactly once?
 */
case class RewriteTactic(
    equations:  Traversable[( String, Boolean )],
    target:     Option[String],
    fixedSubst: Map[Var, Expr],
    once:       Boolean ) extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) = target match {
    case Some( tgt ) => apply( goal, tgt ).flatMap( replace( _ ) )
    case _ => goal.labelledSequent match {
      case Sequent( _, Seq( ( tgt, _ ) ) ) => apply( goal, tgt ).flatMap( replace( _ ) )
      case _                               => TacticFailure( this, "target formula not found" )
    }
  }

  def apply( goal: OpenAssumption, target: String ): Tactic[LKProof] = {
    for {
      ( eqLabel, leftToRight ) <- equations
      ( ( `target`, tgt ), tgtIdx ) <- goal.labelledSequent.zipWithIndex.elements
      ( `eqLabel`, quantEq @ All.Block( vs, eq @ Eq( t, s ) ) ) <- goal.labelledSequent.antecedent
      ( t_, s_ ) = if ( leftToRight ) ( t, s ) else ( s, t )
      pos <- HOLPosition getPositions tgt
      subst <- syntacticMatching( List( t_ -> tgt( pos ) ), PreSubstitution( fixedSubst ++ freeVariables( quantEq ).map { v => v -> v } ) )
    } return {
      val newTgt = tgt.replace( pos, subst( s_ ) )
      val newGoal = OpenAssumption( goal.labelledSequent.updated( tgtIdx, target -> newTgt ) )
      for {
        p1 <- if ( once ) Tactic.pure( newGoal ) else apply( newGoal, target ) orElse Tactic.pure( newGoal )
        p2 = WeakeningLeftRule( p1, subst( eq ) )
        p3 = if ( tgtIdx isSuc ) EqualityRightRule( p2, Ant( 0 ), newTgt, tgt )
        else EqualityLeftRule( p2, Ant( 0 ), newTgt, tgt )
        p4 = ForallLeftBlock( p3, quantEq, subst( vs ) )
        p5 = ContractionLeftRule( p4, quantEq )
        _ = require( p5.conclusion multiSetEquals goal.conclusion )
      } yield p5
    }
    if ( once ) TacticFailure( this, "cannot rewrite at least once" ) else Tactic.pure( goal )
  }

  def ltr( eqs: String* ) = copy( equations = equations ++ eqs.map { _ -> true } )
  def rtl( eqs: String* ) = copy( equations = equations ++ eqs.map { _ -> false } )
  def in( tgt: String ) = copy( target = Some( tgt ) )
  def many = copy( once = false )
  def subst( s: ( Var, Expr )* ) = copy( fixedSubst = fixedSubst ++ s )
}

/**
 * Reduces a subgoal via induction.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param ctx  A [[gapt.proofs.context.Context]]. Used to find the constructors of inductive types.
 */
case class InductionTactic( mode: TacticApplyMode, v: Var, eigenVariables: Map[Const, Vector[Var]] = Map() )( implicit ctx: Context ) extends Tactical1[Unit] {

  /**
   * Reads the constructors of type `t` from the context.
   *
   * @param t A base type.
   * @return Either a list containing the constructors of `t` or a TacticalFailure.
   */
  private def getConstructors( t: TBase ): Tactic[Seq[Const]] = {
    ( ctx.isType( t ), ctx.getConstructors( t ) ) match {
      case ( true, Some( constructors ) ) => Tactic.pure( constructors )
      case ( true, None )                 => TacticFailure( this, s"Type $t is not inductively defined" )
      case ( false, _ )                   => TacticFailure( this, s"Type $t is not defined" )
    }
  }

  def withEigenVariables( evs: Map[Const, Vector[Var]] ): InductionTactic =
    copy( eigenVariables = evs )

  def apply( goal: OpenAssumption ): Tactic[Unit] =
    for {
      ( label, main, idx: Suc ) <- findFormula( goal, mode )
      formula = main
      constrs <- getConstructors( v.ty.asInstanceOf[TBase] )
      cases = constrs.map { constr =>
        val FunctionType( _, argTypes ) = constr.ty
        val nameGen = rename.awayFrom( freeVariables( goal.conclusion ) )
        val evs = eigenVariables.getOrElse( constr, argTypes map { at => nameGen.fresh( if ( at == v.ty ) v else Var( "x", at ) ) } )
        val hyps = NewLabels( goal.labelledSequent, s"IH${v.name}" ) zip ( evs filter { _.ty == v.ty } map { ev => Substitution( v -> ev )( formula ) } )
        val subGoal = hyps ++: goal.labelledSequent.delete( idx ) :+ ( label -> Substitution( v -> constr( evs: _* ) )( formula ) )
        InductionCase( OpenAssumption( subGoal ), constr, subGoal.indices.take( hyps.size ), evs, subGoal.indices.last )
      }
      _ <- replace( InductionRule( cases, Abs( v, main ), v ) )
    } yield ()
}

case class UnfoldTacticHelper( definitions: Seq[String], maxSteps: Option[Int] = None )( implicit ctx: Context ) {
  def atMost( steps: Int ): UnfoldTacticHelper = copy( maxSteps = Some( steps ) )

  def in( labels: String* ) = labels.foldLeft[Tactic[Unit]]( skip ) {
    ( acc, l ) => acc andThen UnfoldTactic( l, definitions, maxSteps )
  }
}

case class UnfoldTactic( target: String, definitions: Seq[String], maxSteps: Option[Int] )( implicit ctx: Context ) extends Tactical1[Unit] {
  def unfold( main: Formula ): Formula = {
    val base = ctx.normalizer
    def normalizeArgs( as: List[Expr], remainingSteps: Int ): ( List[Expr], Int ) =
      as match {
        case Nil => ( Nil, remainingSteps )
        case a :: as_ =>
          val ( a_, remainingSteps_ ) = normalize( a, remainingSteps )
          val ( as__, remainingSteps__ ) = normalizeArgs( as_, remainingSteps_ )
          ( a_ :: as__, remainingSteps__ )
      }
    def normalize( expr: Expr, remainingSteps: Int ): ( Expr, Int ) = {
      val Apps( hd, as ) = expr
      ( hd match {
        case Const( n, _, _ ) =>
          if ( !definitions.contains( n ) )
            ( None, remainingSteps )
          else if ( remainingSteps == 0 )
            ( None, remainingSteps )
          else
            ( base.reduce1( expr ), remainingSteps - 1 )
        case _ =>
          ( base.reduce1( expr ), remainingSteps )
      } ) match {
        case ( Some( expr_ ), remainingSteps_ ) =>
          normalize( expr_, remainingSteps_ )
        case ( None, _ ) =>
          hd match {
            case Abs.Block( vs, sub ) if vs.nonEmpty =>
              val ( sub_, remainingSteps_ ) = normalize( sub, remainingSteps )
              Abs.Block( vs, sub_ ) -> remainingSteps_
            case _ =>
              val ( as_, remainingSteps_ ) = normalizeArgs( as, remainingSteps )
              ( hd( as_ ), remainingSteps_ )
          }
      }
    }

    normalize( main, maxSteps.getOrElse( -1 ) )._1.asInstanceOf[Formula]
  }

  def apply( goal: OpenAssumption ): Tactic[Unit] =
    for {
      ( label: String, main: Formula, idx: SequentIndex ) <- findFormula( goal, OnLabel( target ) )
      newGoal = OpenAssumption( goal.labelledSequent.updated( idx, label -> unfold( main ) ) )
      _ <- replace( DefinitionRule( newGoal, idx, main ) )
    } yield ()
}

/**
 * Calls the GAPT tableau prover on the subgoal.
 */
case object PropTactic extends Tactical1[Unit] {
  override def apply( goal: OpenAssumption ): Tactic[Unit] =
    solvePropositional( goal.conclusion ) match {
      case Left( err )    => TacticFailure( this, s"found model:\n$err" )
      case Right( proof ) => replace( proof )
    }
}

case object QuasiPropTactic extends Tactical1[Unit] {
  override def apply( goal: OpenAssumption ) =
    solveQuasiPropositional( goal.conclusion ) match {
      case Left( err )    => TacticFailure( this, s"search failed on atomic sequent:\n$err" )
      case Right( proof ) => replace( proof )
    }
}

case class ResolutionProverTactic(
    prover:            Prover,
    viaExpansionProof: Boolean = true,
    deskolemize:       Boolean = false )( implicit ctx: MutableContext ) extends Tactical1[Unit] {
  def withDeskolemization: ResolutionProverTactic = copy( deskolemize = true )

  override def apply( goal: OpenAssumption ): Tactic[Unit] = {
    val proofOption: Option[LKProof] =
      if ( deskolemize )
        prover.getExpansionProof( goal.conclusion )
          .map( deskolemizeET( _ ) )
          .map( ExpansionProofToLK( _ ).right.get )
      else if ( viaExpansionProof )
        prover.getExpansionProof( goal.conclusion )
          .map( ExpansionProofToLK( _ ).right.get )
      else
        prover.getLKProof( goal.conclusion )
    proofOption match {
      case None       => TacticFailure( this, "search failed" )
      case Some( lk ) => replace( lk )
    }
  }
}

object AnalyticInductionTactic {
  def sequentialAxioms = SequentialInductionAxioms()
  def independentAxioms = IndependentInductionAxioms()
  def standardAxioms = StandardInductionAxioms()
  def domainClosure = DomainClosureAxioms()
  def tipDomainClosure = TipDomainClosureAxioms()
}
/**
 * Calls the analytic induction prover on the subgoal
 */
case class AnalyticInductionTactic( axioms: AxiomFactory, prover: ResolutionProver )( implicit ctx: MutableContext ) extends Tactical1[Unit] {
  override def apply( goal: OpenAssumption ) =
    AnalyticInductionProver( axioms, prover ) inductiveLKProof ( goal.labelledSequent ) match {
      case None       => TacticFailure( this, "analytic induction prover failed" )
      case Some( lk ) => replace( lk )
    }

  def withAxioms( axiom: AxiomFactory ): AnalyticInductionTactic =
    copy( axioms = axiom )

  def withProver( prover: ResolutionProver ): AnalyticInductionTactic =
    copy( prover = prover )
}

case class SubstTactic( mode: TacticApplyMode ) extends Tactical1[Unit] {

  private object VEq {
    def unapply( f: Formula ): Option[( Expr, Expr, Boolean )] =
      f match {
        case Eq( t: Var, s ) => Some( ( t, s, true ) )
        case Eq( t, s: Var ) => Some( ( t, s, false ) )
        case _               => None
      }
  }

  private def mkProof( subst: Substitution, t: Expr, s: Expr, vLeft: Boolean, q: LKProof, todo: List[( Formula, Polarity )] ): LKProof =
    todo match {
      case Nil => q
      case ( f, _ ) :: todo_ if freeVariables( f ).intersect( subst.domain ).isEmpty =>
        mkProof( subst, t, s, vLeft, q, todo_ )
      case ( f, pol ) :: todo_ if pol.inAnt =>
        mkProof( subst, t, s, vLeft, EqualityLeftRule( q, t === s, subst( f ), f ), todo_ )
      case ( f, pol ) :: todo_ if pol.inSuc =>
        mkProof( subst, t, s, vLeft, EqualityRightRule( q, t === s, subst( f ), f ), todo_ )
    }

  def apply( goal: OpenAssumption ): Tactic[Unit] =
    for {
      ( existingLabel: String, VEq( t, s, vLeft ), i: Ant ) <- findFormula( goal, mode )
      subst = Substitution( if ( vLeft ) t.asInstanceOf[Var] -> s else s.asInstanceOf[Var] -> t )
      newGoal = subst( goal.labelledSequent.delete( i ) )
      _ <- replace(
        mkProof( subst, t, s, vLeft,
          WeakeningLeftRule(
            OpenAssumption( newGoal ), t === s ),
          goal.endSequent.delete( i ).polarizedElements.toList ) )
    } yield ()
}
