package at.logic.gapt.proofs.resolution

import at.logic.gapt.examples.CountingEquivalence
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class StructuralCNFTest extends Specification {

  "default" in {
    val cnf = structuralCNF(
      Sequent() :+ CountingEquivalence( 3 ),
      propositional = false, structural = true, bidirectionalDefs = false
    )
    Escargot.getResolutionProof( cnf ) must beSome
  }

  "bidirectional definitions" in {
    val cnf = structuralCNF(
      Sequent() :+ CountingEquivalence( 3 ),
      propositional = false, structural = true, bidirectionalDefs = true
    )
    Escargot.getResolutionProof( cnf ) must beSome
  }

  "non-structural" in {
    val cnf = structuralCNF(
      Sequent() :+ CountingEquivalence( 0 ),
      propositional = false, structural = false, bidirectionalDefs = false
    )
    Escargot.getResolutionProof( cnf ) must beSome
  }

}
