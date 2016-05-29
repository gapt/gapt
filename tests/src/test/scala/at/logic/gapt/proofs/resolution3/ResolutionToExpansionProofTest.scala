package at.logic.gapt.proofs.resolution3

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class ResolutionToExpansionProofTest extends Specification with SatMatchers{

  "linear" in {
    val ep = ResolutionToExpansionProof.withDefs(resOld2New(Escargot getRobinsonProof hof"p 0 & !x (p x -> p (s x)) -> p (s (s 0))" get))
    ep.deep must beValidSequent
  }

  "non-empty conclusion" in {
    val cnf = structuralCNF3(BussTautology(5), false)
    for (p <- cnf)
      ResolutionToExpansionProof(p)
    ok
  }

}
