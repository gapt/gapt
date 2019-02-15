package gapt.proofs

import gapt.expr._
import gapt.logic.Polarity

package object expansion {
  type ExpansionSequent = Sequent[ExpansionTree]
  val ExpansionSequent = Sequent

  /**
   * Extension class that allows calling shallow and deep on sequents.
   *
   * @param sequent The expansion sequent that this wraps around.
   */
  implicit class RichExpansionSequent( private val sequent: ExpansionSequent ) extends AnyVal {
    def shallow: HOLSequent = sequent.map( _.shallow )
    def deep: HOLSequent = sequent.map( _.deep )

    def toDisjunction( polarity: Polarity ): ExpansionTree =
      sequent.map( ETNeg( _ ), identity ).
        elements.
        reduceOption( ETOr( _, _ ) ).
        getOrElse( ETBottom( polarity ) )
  }
}
