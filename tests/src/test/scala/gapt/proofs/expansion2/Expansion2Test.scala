package gapt.proofs.expansion2

import gapt.examples.Pi3Pigeonhole
import gapt.proofs.lk.LKToExpansionProof
import org.specs2.mutable.Specification
import gapt.provers.smtlib.SmtInterpol

class Expansion2Test extends Specification {

  "pigeon" in {
    val exp = eliminateCutsET( ETtoET2( LKToExpansionProof( Pi3Pigeonhole.proof ) ) )
    SmtInterpol.isValid( exp.deep ) must_== true
  }

}
