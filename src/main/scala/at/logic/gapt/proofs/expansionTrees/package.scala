package at.logic.gapt.proofs

import at.logic.gapt.proofs.lk.base.Sequent

/**
 * Created by sebastian on 7/15/15.
 */
package object expansionTrees {
  type ExpansionSequent = Sequent[ExpansionTree]

  implicit class RichExpansionsequent( seq: ExpansionSequent ) {
    def polarizedTrees = seq.polarizedElements
  }
}
