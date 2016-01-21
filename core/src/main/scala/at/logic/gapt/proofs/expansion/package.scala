package at.logic.gapt.proofs

import at.logic.gapt.expr.ClosedUnderSub

package object expansion {
  type ExpansionSequent = Sequent[ExpansionTree]
  val ExpansionSequent = Sequent

  implicit val expansionTreesAreClosedUnderAdmissibleSubstitutions: ClosedUnderSub[ExpansionTree] = expansionTreeSubstitution
  implicit val expansionProofsAreClosedUnderSubstitution: ClosedUnderSub[ExpansionProofWithCut] = expansionProofSubstitution
}
