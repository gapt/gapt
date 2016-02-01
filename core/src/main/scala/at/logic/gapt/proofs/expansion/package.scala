package at.logic.gapt.proofs

import at.logic.gapt.expr.ClosedUnderSub

package object expansion {
  type ExpansionSequent = Sequent[ExpansionTree]
  val ExpansionSequent = Sequent

  /**
   * Extension class that allows calling shallow and deep on sequents.
   *
   * @param sequent The expansion sequent that this wraps around.
   */
  implicit class RichExpansionSequent( val sequent: ExpansionSequent ) {
    def shallow = sequent map { _.shallow }
    def deep = sequent map { _.deep }
  }

  implicit val expansionTreesAreClosedUnderAdmissibleSubstitutions: ClosedUnderSub[ExpansionTree] = expansionTreeSubstitution
  implicit val expansionProofsAreClosedUnderSubstitution: ClosedUnderSub[ExpansionProofWithCut] = expansionProofSubstitution
}
