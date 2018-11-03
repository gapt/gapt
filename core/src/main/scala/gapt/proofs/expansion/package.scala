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
}
