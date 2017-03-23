package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{ Apps, Expr, Formula, Substitution, Var }
import at.logic.gapt.proofs.{ Sequent, SequentConnector }

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
      }
    )
    val argumentProofs = primaryArguments map (
      argument => {
        unfoldInduction( InductionRule( inductionCases, inductionFormula, argument ) )
      }
    )

    val Seq( inductionCase ) = inductionCases filter { _.constructor == constructor }

    val proofWithRedundancy = argumentProofs.foldRight( inductionStepProof( arguments, inductionCase ) )(
      ( argumentProof, mainProof ) => {
        CutRule( argumentProof, mainProof, argumentProof.endSequent.succedent.last )
      }
    )

    eliminateRedundantFormulas( proofWithRedundancy, proof.endSequent )
  }

  /**
   * Eliminates redundant formulas by applying contractions.
   *
   * @param proof The proof from which the redundant formulas are to be eliminated.
   * @param sequent The proof's end-sequent should contain exactly the formulas of this sequent.
   * @return A proof of the given sequent that is obtained from proof by applying left and right
   *         contractions.
   */
  private def eliminateRedundantFormulas( proof: LKProof, sequent: Sequent[Formula] ): LKProof = {
    val contractedAntecedentProof = sequent.antecedent.foldRight( proof ) { ( formula, contractedProof ) =>
      ContractionLeftMacroRule( contractedProof, formula, sequent.antecedent.filter( _ == formula ).size )
    }
    sequent.succedent.foldRight( contractedAntecedentProof ) { ( formula, contractedProof ) =>
      ContractionRightMacroRule( contractedProof, formula, sequent.succedent.filter( _ == formula ).size )
    }
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
    val substitution = new Substitution(
      Map[Var, Expr]( eigenVariables.zip( arguments ): _* )
    )
    LKProofSubstitutableDefault.applySubstitution( substitution, proof )
  }

}

