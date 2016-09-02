package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.fol.{ Numeral, isFOLPrenexSigma1 }
import at.logic.gapt.expr._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class PrenexifyETTest extends Specification with SatMatchers {
  "linear" in {
    val Some( expansion ) = Escargot.getExpansionProof( hof"!y p 0 y & !x (?y p x y -> !y p (s x) y) -> p ${Numeral( 9 )} c" )
    val prenex = prenexifyET( expansion )
    isFOLPrenexSigma1( prenex.shallow ) must_== true
    prenex.deep must beValidSequent
  }
}
