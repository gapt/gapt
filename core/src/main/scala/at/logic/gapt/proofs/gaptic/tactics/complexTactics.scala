package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import scalaz._
import Scalaz._
import Validation.FlatMap._

/**
 * Repeatedly applies unary rules that are unambiguous
 */
case object DecomposeTactic extends Tactical[Unit] {
  def apply( proofState: ProofState ) = {
    RepeatTactic(
      NegLeftTactic() orElse
        NegRightTactic() orElse
        AndLeftTactic() orElse
        OrRightTactic() orElse
        ImpRightTactic() orElse
        ForallRightTactic() orElse
        ExistsLeftTactic()
    )( proofState )
  }
}

case class DestructTactic( applyToLabel: String ) extends Tactic[Any] {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.elements )
        yield index

    // Select some formula index!
    indices.headOption match {
      case Some( i ) =>
        val ( existingLabel, _ ) = goalSequent( i )

        val tac = allR( existingLabel ) orElse
          exL( existingLabel ) orElse
          andL( existingLabel ) orElse
          andR( existingLabel ) orElse
          orL( existingLabel ) orElse
          orR( existingLabel ) orElse
          impL( existingLabel ) orElse
          impR( existingLabel ) orElse
          negL( existingLabel ) orElse
          negR( existingLabel )
        tac( goal )
      case None => TacticalFailure( this, Some( goal ), "no destructable formula found" ).failureNel
    }
  }
}

/**
 * Chain
 */
case class ChainTactic( hyp: String, target: Option[String] = None, substitution: Map[Var, LambdaExpression] = Map() ) extends Tactic[Unit] {

  def subst( map: ( Var, LambdaExpression )* ) = copy( substitution = substitution ++ map )

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    // Proceed only if a (universally quantified) hypothesis exists
    ( for ( ( ( `hyp`, All( _, _ ) ), index: Ant ) <- goalSequent.zipWithIndex.elements ) yield index ).headOption.
      toSuccessNel( TacticalFailure( this, Some( goal ), s"hyp $hyp not found" ) ) flatMap { hypIndex =>

        // Extract hypothesis
        val ( _, quantifiedFormula ) = goalSequent( hypIndex )
        val All.Block( hypVar, hypInner ) = quantifiedFormula

        // Extract formula to match against target
        def f( x: HOLFormula ): HOLFormula = x match {
          case Imp( _, r ) => f( r )
          case _           => x
        }

        val hypTargetMatch = f( hypInner )

        // Find target index and substitution
        ( target match {
          case Some( x ) =>
            ( for (
              ( ( `x`, y ), index ) <- goalSequent.zipWithIndex.succedent;
              sub <- syntacticMatching( List( hypTargetMatch -> y ), substitution )
            ) yield ( x, index, sub ) ).headOption
          case None =>
            ( for (
              ( ( x, y ), index ) <- goalSequent.zipWithIndex.succedent;
              sub <- syntacticMatching( List( hypTargetMatch -> y ), substitution )
            ) yield ( x, index, sub ) ).headOption
        } ).toSuccessNel( TacticalFailure( this, Some( goal ), s"target $target not found" ) ) map {

          // Proceed only if a matching formula exists
          case ( targetLabel, targetIndex, sub ) =>

            // Recursively apply implication left to the left until the end of the chain is reached,
            // where the sequent is an axiom (following some contractions).
            // The right premises of the implication left rules become new sub goals,
            // but where the initial target formula is then "forgotten".
            def handleAnds( curGoal: Sequent[( String, HOLFormula )], hypCond: Suc ): LKProof = curGoal( hypCond ) match {
              case ( existingLabel, And( lhs, rhs ) ) =>
                AndRightRule(
                  handleAnds( curGoal.updated( hypCond, existingLabel -> lhs ), hypCond ),
                  handleAnds( curGoal.updated( hypCond, existingLabel -> rhs ), hypCond ),
                  And( lhs, rhs )
                )
              case _ =>
                OpenAssumption( curGoal )
            }

            def handleImps( curGoal: Sequent[( String, HOLFormula )], hyp: Ant ): LKProof = {
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
            val newGoal = ( NewLabel( goalSequent, hyp ) -> auxFormula ) +: goalSequent
            val premise = handleImps( newGoal, Ant( 0 ) )
            val auxProofSegment = ForallLeftBlock( premise, quantifiedFormula, sub( hypVar ) )
            () -> ContractionLeftRule( auxProofSegment, quantifiedFormula )

        }

      }
  }

  def at( target: String ) = new ChainTactic( hyp, Option( target ) )
}

/**
 * Paramodulation tactic
 */
case class ParamodulationTactic( mainFormulaLabel: String, axiom: HOLAtom, targetFormula: HOLFormula ) extends Tactic[Unit] {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = for ( ( ( `mainFormulaLabel`, _ ), index ) <- goalSequent.zipWithIndex.elements )
      yield index

    indices.headOption match {
      case Some( sequentIndex ) =>

        axiom match {
          case Eq( _, _ ) =>

            val cutLabel = NewLabel( goalSequent, mainFormulaLabel + "_cut" )

            val leftPremise = TheoryAxiom( Sequent( Nil, Seq( axiom ) ) )
            val rightPremiseTmp = OpenAssumption( ( cutLabel, axiom ) +: goalSequent )

            val ( cutIndex, rightPremise ) = sequentIndex match {
              case Ant( _ ) =>
                ( Ant( 1 ), eqL( cutLabel, mainFormulaLabel ).to( targetFormula )( rightPremiseTmp ) )
              case Suc( _ ) =>
                ( Ant( 0 ), eqR( cutLabel, mainFormulaLabel ).to( targetFormula )( rightPremiseTmp ) )
            }

            rightPremise map { case ( _, p ) => () -> CutRule( leftPremise, Suc( 0 ), p, cutIndex ) }

          case _ => TacticalFailure( this, Some( goal ), "not an equation" ).failureNel
        }

      case None => TacticalFailure( this, Some( goal ), "label not found" ).failureNel
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
    equations: Traversable[( String, Boolean )],
    target:    Option[String],
    once:      Boolean
) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = target match {
    case Some( tgt ) => apply( goal, tgt ) map { () -> _ }
    case _ => goal.s match {
      case Sequent( _, Seq( ( tgt, _ ) ) ) => apply( goal, tgt ) map { () -> _ }
      case _                               => TacticalFailure( this, Some( goal ), "target formula not found" ).failureNel
    }
  }

  def apply( goal: OpenAssumption, target: String ): ValidationNel[TacticalFailure, LKProof] = {
    for {
      ( eqLabel, leftToRight ) <- equations
      ( ( `target`, tgt ), tgtIdx ) <- goal.s.zipWithIndex.elements
      ( `eqLabel`, quantEq @ All.Block( vs, eq @ Eq( t, s ) ) ) <- goal.s.antecedent
      ( t_, s_ ) = if ( leftToRight ) ( t, s ) else ( s, t )
      pos <- HOLPosition getPositions tgt
      subst <- syntacticMatching( t_, tgt( pos ) )
    } return {
      val newTgt = tgt.replace( pos, subst( s_ ) )
      val newGoal = OpenAssumption( goal.s.updated( tgtIdx, target -> newTgt ) )
      val p1 = if ( once ) newGoal else apply( newGoal, target ) getOrElse newGoal
      val p2 = WeakeningLeftRule( p1, subst( eq ) )
      val p3 =
        if ( tgtIdx isSuc ) EqualityRightRule( p2, Ant( 0 ), newTgt, tgt )
        else EqualityLeftRule( p2, Ant( 0 ), newTgt, tgt )
      val p4 = ForallLeftBlock( p3, quantEq, subst( vs ) )
      val p5 = ContractionLeftRule( p4, quantEq )
      require( p5.conclusion multiSetEquals goal.conclusion )
      p5.success
    }
    if ( once ) TacticalFailure( this, Some( goal ), "cannot rewrite at least once" ).failureNel else goal.success
  }

  def ltr( eqs: String* ) = copy( equations = equations ++ eqs.map { _ -> true } )
  def rtl( eqs: String* ) = copy( equations = equations ++ eqs.map { _ -> false } )
  def in( tgt: String ) = copy( target = Some( tgt ) )
  def many = copy( once = false )
}

/**
 * Solves propositional sub goal
 */
case object PropTactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) = {
    solve.solvePropositional( goal.conclusion ).toSuccessNel( TacticalFailure( this, Some( goal ), "search failed" ) ) map { () -> _ }
  }
}

/**
 * Solves sub goal with Prover9
 */
case object Prover9Tactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) = {
    Prover9.getLKProof( goal.conclusion ).toSuccessNel( TacticalFailure( this, Some( goal ), "search failed" ) ) map { () -> _ }
  }
}

case object EscargotTactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) =
    Escargot getLKProof goal.conclusion toSuccessNel TacticalFailure( this, Some( goal ), "search failed" ) map { () -> _ }
}
