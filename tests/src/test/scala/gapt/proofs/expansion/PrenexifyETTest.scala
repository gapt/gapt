package gapt.proofs.expansion

import gapt.expr.formula.fol.{Numeral, isFOLPrenexSigma1}
import gapt.expr._
import gapt.provers.escargot.Escargot
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class PrenexifyETTest extends Specification with SatMatchers {
  "linear" in {
    val Some(expansion) = Escargot.getExpansionProof(hof"!y p 0 y & !x (?y p x y -> !y p (s x) y) -> p ${Numeral(9)} c"): @unchecked
    val prenex = prenexifyET(expansion)
    isFOLPrenexSigma1(prenex.shallow) must_== true
    prenex.deep must beValidSequent
  }
}
