package gapt.proofs.lk

import gapt.expr.{ Apps, Expr, Formula, Substitution, Var }
import gapt.proofs.{ Sequent, SequentConnector }

object unfoldInduction {

  /**
   * Unfolds an induction induction inference.
   *
   * @param proof A regular proof with an induction inference as its last inference.
   *              The induction must be a ground term in constructor form.
   * @return
   */
  def apply( proof: InductionRule ): LKProof = {
    val InductionRule( inductionCases, inductionFormula, inductionTerm ) = proof
    val inductionType = inductionTerm.ty
    val Apps( constructor, arguments ) = inductionTerm
    val ( primaryArguments, _ ) = arguments.partition(
      argument => {
        argument.ty == inductionType
      } )
    val argumentProofs = primaryArguments map (
      argument => {
        unfoldInduction( InductionRule( inductionCases, inductionFormula, argument ) )
      } )

    val Seq( inductionCase ) = inductionCases filter { _.constructor == constructor }

    val proofWithRedundancy = argumentProofs.foldRight( inductionStepProof( arguments, inductionCase ) )(
      ( argumentProof, mainProof ) => {
        CutRule( argumentProof, mainProof, argumentProof.endSequent.succedent.last )
      } )
    WeakeningMacroRule(
      ContractionMacroRule( proofWithRedundancy, proof.endSequent, false ),
      proof.endSequent, false )
  }

  /**
   * Instantiates the proof of an induction step.
   *
   * @param arguments The eigenvariables of the induction step are substituted by these terms.
   * @param inductionCase The induction case that is to be instantiated with the given terms.
   * @return The induction step instantiated for the given terms. The substitution is with respect to the ordering
   *         of the eigenvariables and the terms, i.e. the first eigenvariable is substituted by the first term, and
   *         so on.
   */
  private def inductionStepProof( arguments: Seq[Expr], inductionCase: InductionCase ): LKProof = {
    val InductionCase( proof, _, _, eigenVariables, _ ) = inductionCase
    Substitution( eigenVariables zip arguments )( proof )
  }

}

