package gapt.proofs.resolution

import gapt.expr._
import gapt.examples.CountingEquivalence
import gapt.proofs.Sequent
import gapt.provers.escargot.Escargot
import gapt.provers.sat.Sat4j
import org.specs2.mutable.Specification

class StructuralCNFTest extends Specification {

  "default" in {
    val cnf = structuralCNF(
      Sequent() :+ CountingEquivalence(3),
      propositional = false,
      structural = true,
      bidirectionalDefs = false
    )
    Escargot.getResolutionProof(cnf) must beSome
  }

  "bidirectional definitions" in {
    val cnf = structuralCNF(
      Sequent() :+ CountingEquivalence(3),
      propositional = false,
      structural = true,
      bidirectionalDefs = true
    )
    Escargot.getResolutionProof(cnf) must beSome
  }

  "non-structural" in {
    val cnf = structuralCNF(
      Sequent() :+ CountingEquivalence(0),
      propositional = false,
      structural = false,
      bidirectionalDefs = false
    )
    Escargot.getResolutionProof(cnf) must beSome
  }

  "bug 652" in {
    val cnf = structuralCNF(
      fos":- a <-> (a <-> true)",
      propositional = true,
      structural = true,
      bidirectionalDefs = false,
      cse = false
    )
    Sat4j.getResolutionProof(cnf) must beSome
  }

}
