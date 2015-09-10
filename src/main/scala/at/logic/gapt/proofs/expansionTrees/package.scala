package at.logic.gapt.proofs

/**
 * Created by sebastian on 7/15/15.
 */
package object expansionTrees {
  type ExpansionSequent = Sequent[ExpansionTree]
  type MultiExpansionSequent = Sequent[MultiExpansionTree]

  implicit class RichExpansionSequent( seq: ExpansionSequent ) {
    def polarizedTrees = seq.polarizedElements
  }

  implicit class RichMultiExpansionSequent( seq: MultiExpansionSequent ) {
    def toDeep = seq map ( _.toDeep( -1 ), _.toDeep( 1 ) )
    def toShallow = seq map ( _.toShallow )
  }
}
