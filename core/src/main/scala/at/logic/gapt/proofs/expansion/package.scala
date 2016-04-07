package at.logic.gapt.proofs

import at.logic.gapt.expr.{ ClosedUnderReplacement, ClosedUnderSub, LambdaExpression, Replaceable }

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
  implicit val expansionProofsAreClosedUnderSubstitution: ClosedUnderSub[ExpansionProof] = expansionProofSubstitution
  implicit val expansionProofsWithCutAreClosedUnderSubstitution: ClosedUnderSub[ExpansionProofWithCut] = expansionProofWithCutSubstitution

  implicit object expansionProofsAreReplaceable extends ClosedUnderReplacement[ExpansionProof] {
    override def replace( proof: ExpansionProof, p: PartialFunction[LambdaExpression, LambdaExpression] ) = replaceET( proof, p )
  }
  implicit object expansionProofsWithCutAreReplaceable extends ClosedUnderReplacement[ExpansionProofWithCut] {
    override def replace( proof: ExpansionProofWithCut, p: PartialFunction[LambdaExpression, LambdaExpression] ) =
      ExpansionProofWithCut( replaceET( proof.expansionWithCutAxiom, p ) )
  }
  implicit object expansionTreesAreReplaceable extends ClosedUnderReplacement[ExpansionTree] {
    override def replace( proof: ExpansionTree, p: PartialFunction[LambdaExpression, LambdaExpression] ) = replaceET( proof, p )
  }
}
