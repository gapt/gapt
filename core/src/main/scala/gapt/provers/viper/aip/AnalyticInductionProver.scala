package gapt.provers.viper.aip

import cats.syntax.all._
import gapt.expr.Var
import gapt.expr.formula.Formula
import gapt.formats.tip.TipProblem
import gapt.proofs.gaptic.{ escargot => escargotTactic }
import gapt.proofs.gaptic._
import gapt.proofs.lk.LKProof
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.lk.rules.CutRule
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.provers.viper.aip.axioms.Axiom
import gapt.provers.viper.aip.axioms.AxiomFactory
import gapt.provers.viper.aip.axioms.SequentialInductionAxioms

case class ProverOptions(
    prover:       ResolutionProver = Escargot,
    axiomFactory: AxiomFactory     = SequentialInductionAxioms() )

object AnalyticInductionProver {

  /**
   * Tries to prove the given sequent by using a single induction on the specified variable.
   *
   * @param sequent  A sequent of the form `Γ, :- ∀x.A`
   * @param variable An eigenvariable `α` for the sequent `Γ, :- ∀x.A`
   * @param ctx      The context which defines the inductive types, etc.
   * @return If the sequent is provable with at most one induction on `α` then a proof which uses a single induction
   *         on the formula `A[x/α]` and variable `α` is returned, otherwise the method does either not terminate or
   *         throws an exception.
   */
  def singleInduction( sequent: Sequent[( String, Formula )], variable: Var )( implicit ctx: MutableContext ): LKProof = {
    var state = ProofState( sequent )
    state += allR( variable );
    state += induction( on = variable )
    state += decompose.onAllSubGoals
    state += repeat( escargotTactic )
    state.result
  }

  /**
   * Creates a new analytic induction prover.
   *
   * @param axioms The axiom factories used by the prover.
   * @param prover The internal prover that is to be used for proof search.
   * @return A new analytic induction prover that uses the provided objects for proof search.
   */
  def apply( axioms: AxiomFactory, prover: ResolutionProver ) = new AnalyticInductionProver(
    new ProverOptions( prover, axioms ) )
}

class AnalyticInductionProver( options: ProverOptions ) {

  private implicit def labeledSequentToHOLSequent( sequent: Sequent[( String, Formula )] ) =
    sequent map { case ( _, f ) => f }

  /**
   * Tries to prove a sequent by using analytic induction.
   *
   * @param sequent The sequent to prove.
   * @param ctx     Defines inductive types etc.
   * @return true if the sequent is provable with analytic induction, otherwise either false or the method does
   *         not terminate.
   */
  def isValid( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ) =
    options.prover.isValid( inductiveSequent( sequent ) )

  /**
   * Tries to compute a LK proof for a sequent by using analytic induction.
   *
   * @param sequent The sequent to prove.
   * @param ctx     Defines inductive types etc.
   * @return An LK proof if the sequent is provable with analytic induction, otherwise either None or the method does
   *         not terminate.
   */
  def lkProof(
    sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ) = options.prover.getLKProof( inductiveSequent( sequent ) )

  /**
   * Proves a TIP problem by using induction.
   *
   * @param problem The problem to prove
   * @return A proof if the problem is provable with the prover's induction schemes, otherwise None or the
   *         method does not terminate.
   */
  def proveTipProblem( problem: TipProblem ): Option[LKProof] =
    inductiveLKProof( tipProblemToSequent( problem )._1 )( problem.ctx.newMutable )

  /**
   * Proves the given sequent by using induction.
   *
   * @param sequent The sequent to be proven.
   * @param ctx Defines the constants, types, etc.
   * @return An inductive proof the sequent is provable with the prover's induction schemes, otherwise None or
   *         the method does not terminate.
   */
  def inductiveLKProof( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): Option[LKProof] = {
    val axioms = validate( options.axiomFactory( sequent ) )
    val prover = options.prover
    for {
      mainProof <- prover.getLKProof( axioms.map( _.formula ) ++: sequent.map( _._2 ) )
    } yield {
      cutAxioms( mainProof, axioms )
    }
  }

  /**
   * Cuts the specified axioms from the proof.
   *
   * @param proof The proof from which some axioms are to be cut. The end-sequent of this proof must
   *              contain the given axioms.
   * @param axioms The axioms to be cut out of the proof.
   * @return A proof whose end-sequent does not contain the specified axioms.
   */
  private def cutAxioms( proof: LKProof, axioms: List[Axiom] ): LKProof =
    axioms.foldRight( proof ) { ( axiom, mainProof ) =>
      if ( mainProof.conclusion.antecedent contains axiom.formula )
        CutRule( axiom.proof, mainProof, axiom.formula )
      else
        mainProof
    }

  /**
   * Tries to compute a resolution proof for a sequent by using analytic induction.
   *
   * @param sequent The sequent to prove.
   * @param ctx     Defines inductive types etc.
   * @return A resolution proof if the sequent is provable with analytic induction, otherwise either None or the
   *         method does not terminate.
   */
  def resolutionProof( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ) =
    options.prover.getResolutionProof( inductiveSequent( sequent ) )

  /**
   * Tries to compute an expansion proof for a sequent by using analytic induction.
   *
   * @param sequent The sequent to prove.
   * @param ctx     Defines inductive types etc.
   * @return An expansion proof if the sequent is provable with analytic induction, otherwise either None or the
   *         method does not terminate.
   */
  def expansionProof( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ) =
    options.prover.getExpansionProof( inductiveSequent( sequent ) )

  /**
   * Extracts the inductive sequent from a validation value.
   *
   * @tparam T the validations success value type
   * @param validation The validation value from which the sequent is extracted.
   * @return A sequent.
   * @throws Exception If the validation value represents a validation failure.
   */
  private def validate[T]( validation: ThrowsError[T] ): T =
    validation.valueOr( e => throw new Exception( e ) )

  /**
   * Computes a sequent enriched by induction axioms.
   *
   * @param sequent The sequent to which induction axioms are added.
   * @param ctx     Defines inductive types etc.
   * @return The original sequent enriched by induction axioms for all free variables and all outer-most universally
   *         quantified variables.
   */
  private def inductiveSequent(
    sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): HOLSequent =
    validate( prepareSequent( sequent ) )

  /**
   * Adds induction axioms for a formula to a given sequent.
   *
   * @param sequent The sequent to which the induction axioms are added.
   * @param ctx     The context which defines types, constants, etc.
   * @return A sequent with induction axioms for the specified formula and variables if label designates a formula
   *         in the given sequent and all of the given variables are of inductive type (w.r.t. the given context).
   *         Otherwise a string describing the error is returned.
   */
  private def prepareSequent(
    sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): ThrowsError[HOLSequent] = {
    for {
      axioms <- options.axiomFactory( sequent )
    } yield {
      axioms.map( {
        _.formula
      } ) ++: labeledSequentToHOLSequent( sequent )
    }
  }
}
