package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.{ ExpansionProofToLK, deskolemizeET }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.proofs.resolution.{ ResolutionToLKProof, eliminateSplitting }
import at.logic.gapt.provers.escargot.{ Escargot, NonSplittingEscargot }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver
import at.logic.gapt.provers.viper.aip.axioms._
import at.logic.gapt.provers.viper.aip.provers.InternalProver
import cats.syntax.all._

/**
 * Performs backwards chaining:
 * A goal of the form `∀x (P(x) → Q(x)), Γ :- Δ, Q(t)` is replaced by the goal `∀x (P(x) → Q(x)), Γ :- Δ, P(t)`.
 *
 * @param hyp
 * @param target
 * @param substitution
 */
case class ChainTactic( hyp: String, target: TacticApplyMode = UniqueFormula, substitution: Map[Var, Expr] = Map() ) extends Tactic[Unit] {

  def subst( map: ( Var, Expr )* ) = copy( substitution = substitution ++ map )
  def at( target: String ) = copy( target = OnLabel( target ) )

  override def apply( goal: OpenAssumption ) = {
    findFormula( goal, OnLabel( hyp ) ).flatMap {
      case ( _, quantifiedFormula @ All.Block( hypVar, hypInner @ Imp.Block( _, hypTargetMatch ) ), _ ) =>

        def getSubst( f: Formula ): Option[Substitution] =
          syntacticMatching( List( hypTargetMatch -> f ), PreSubstitution( substitution ++ freeVariables( quantifiedFormula ).map( v => v -> v ) ) ).headOption

        // Find target index and substitution
        findFormula( goal, target ).withFilter { case ( _, f, idx ) => idx.isSuc && getSubst( f ).isDefined }.map {
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
                  And( lhs, rhs )
                )
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
            () -> ContractionLeftRule( auxProofSegment, quantifiedFormula )
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
    once:       Boolean
) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = target match {
    case Some( tgt ) => apply( goal, tgt ) map { () -> _ }
    case _ => goal.labelledSequent match {
      case Sequent( _, Seq( ( tgt, _ ) ) ) => apply( goal, tgt ) map { () -> _ }
      case _                               => Left( TacticalFailure( this, "target formula not found" ) )
    }
  }

  def apply( goal: OpenAssumption, target: String ): Either[TacticalFailure, LKProof] = {
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
      val p1 = if ( once ) newGoal else apply( newGoal, target ) getOrElse newGoal
      val p2 = WeakeningLeftRule( p1, subst( eq ) )
      val p3 =
        if ( tgtIdx isSuc ) EqualityRightRule( p2, Ant( 0 ), newTgt, tgt )
        else EqualityLeftRule( p2, Ant( 0 ), newTgt, tgt )
      val p4 = ForallLeftBlock( p3, quantEq, subst( vs ) )
      val p5 = ContractionLeftRule( p4, quantEq )
      require( p5.conclusion multiSetEquals goal.conclusion )
      Right( p5 )
    }
    if ( once ) Left( TacticalFailure( this, "cannot rewrite at least once" ) ) else Right( goal )
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
 * @param ctx A [[at.logic.gapt.proofs.Context]]. Used to find the constructors of inductive types.
 */
case class InductionTactic( mode: TacticApplyMode, v: Var )( implicit ctx: Context ) extends Tactic[Unit] {

  /**
   * Reads the constructors of type `t` from the context.
   *
   * @param t A base type.
   * @return Either a list containing the constructors of `t` or a TacticalFailure.
   */
  private def getConstructors( t: TBase ): Either[TacticalFailure, Seq[Const]] = {
    ( ctx.isType( t ), ctx.getConstructors( t ) ) match {
      case ( true, Some( constructors ) ) => Right( constructors )
      case ( true, None )                 => Left( TacticalFailure( this, s"Type $t is not inductively defined" ) )
      case ( false, _ )                   => Left( TacticalFailure( this, s"Type $t is not defined" ) )
    }
  }

  def apply( goal: OpenAssumption ) =
    for {
      ( label, main, idx: Suc ) <- findFormula( goal, mode )
      formula = main
      constrs <- getConstructors( v.ty.asInstanceOf[TBase] )
    } yield {
      val cases = constrs map { constr =>
        val FunctionType( _, argTypes ) = constr.ty
        var nameGen = rename.awayFrom( freeVariables( goal.conclusion ) )
        val evs = argTypes map { at => nameGen.fresh( if ( at == v.ty ) v else Var( "x", at ) ) }
        val hyps = NewLabels( goal.labelledSequent, s"IH${v.name}" ) zip ( evs filter { _.ty == v.ty } map { ev => Substitution( v -> ev )( formula ) } )
        val subGoal = hyps ++: goal.labelledSequent.delete( idx ) :+ ( label -> Substitution( v -> constr( evs: _* ) )( formula ) )
        InductionCase( OpenAssumption( subGoal ), constr, subGoal.indices.take( hyps.size ), evs, subGoal.indices.last )
      }
      () -> InductionRule( cases, Abs( v, main ), v )
    }
}

case class UnfoldTacticHelper( definitions: Seq[String] )( implicit ctx: Context ) {
  def in( labels: String* ) = labels.foldLeft[Tactical[Unit]]( skip ) {
    ( acc, l ) => acc andThen UnfoldTactic( l, definitions )
  }
}

case class UnfoldTactic( target: String, definitions: Seq[String] )( implicit ctx: Context ) extends Tactic[Unit] {
  def unfold( main: Formula ): Formula = {
    val defsToUnfold = ctx.get[Context.Definitions].filter( definitions contains _._1 )
    normalize( ReductionRule( defsToUnfold, BetaReduction ), main ).asInstanceOf[Formula]
  }

  def apply( goal: OpenAssumption ) =
    for {
      ( label: String, main: Formula, idx: SequentIndex ) <- findFormula( goal, OnLabel( target ) )
      newGoal = OpenAssumption( goal.labelledSequent.updated( idx, label -> unfold( main ) ) )
    } yield () -> DefinitionRule( newGoal, idx, main )
}

/**
 * Calls the GAPT tableau prover on the subgoal.
 */
case object PropTactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) =
    solvePropositional( goal.conclusion ).
      leftMap( err => TacticalFailure( this, s"found model:\n$err" ) ).
      map( () -> _ )
}

case object QuasiPropTactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) =
    solveQuasiPropositional( goal.conclusion ).
      leftMap( err => TacticalFailure( this, s"search failed on atomic sequent:\n$err" ) ).
      map( () -> _ )
}

/**
 * Calls prover9 on the subgoal.
 */
case object Prover9Tactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) =
    Prover9.getLKProof( goal.conclusion ) match {
      case None       => Left( TacticalFailure( this, "search failed" ) )
      case Some( lk ) => Right( () -> lk )
    }
}

/**
 * Calls Escargot on the subgoal.
 */
case object EscargotTactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) =
    Escargot.getExpansionProof( goal.conclusion ) match {
      case None              => Left( TacticalFailure( this, "search failed" ) )
      case Some( expansion ) => Right( () -> ExpansionProofToLK( expansion ).right.get )
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
case class AnalyticInductionTactic( axioms: AxiomFactory, prover: InternalProver )( implicit ctx: Context ) extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) =
    AnalyticInductionProver( axioms, prover ) inductiveLKProof ( goal.labelledSequent ) match {
      case None       => Left( TacticalFailure( this, "search failed" ) )
      case Some( lk ) => Right( () -> lk )
    }

  def withAxioms( axiom: AxiomFactory ): AnalyticInductionTactic =
    copy( axioms = axiom )

  def withProver( prover: InternalProver ): AnalyticInductionTactic =
    copy( prover = prover )
}

