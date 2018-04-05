package gapt.proofs

import gapt.expr.{ ClosedUnderReplacement, ClosedUnderSub, Expr, Polarity, containedNames }

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

    def toDisjunction( polarity: Polarity ) =
      sequent.map( ETNeg( _ ), identity ).
        elements.
        reduceOption( ETOr( _, _ ) ).
        getOrElse( ETBottom( polarity ) )
  }

  implicit val expansionTreesAreClosedUnderAdmissibleSubstitutions: ClosedUnderSub[ExpansionTree] = expansionTreeSubstitution
  implicit val expansionProofsAreClosedUnderSubstitution: ClosedUnderSub[ExpansionProof] = expansionProofSubstitution

  implicit object expansionTreesAreReplaceable extends ClosedUnderReplacement[ExpansionTree] {
    override def replace( proof: ExpansionTree, p: PartialFunction[Expr, Expr] ) = replaceET( proof, p )

    def names( proof: ExpansionTree ) =
      proof.subProofs flatMap {
        case p: ETSkolemQuantifier => containedNames( p.shallow ) ++ containedNames( p.skolemDef )
        case p: ETStrongQuantifier => containedNames( p.shallow ) + p.eigenVariable
        case p                     => containedNames( p.shallow )
      }
  }
  implicit object expansionProofsAreReplaceable extends ClosedUnderReplacement[ExpansionProof] {
    override def replace( proof: ExpansionProof, p: PartialFunction[Expr, Expr] ) = replaceET( proof, p )
    def names( proof: ExpansionProof ) = containedNames( proof.expansionSequent )
  }
}
