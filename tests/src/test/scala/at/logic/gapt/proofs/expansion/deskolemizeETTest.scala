package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.Polarity.{ Negative, Positive }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class deskolemizeETTest extends Specification with SatMatchers {

  "DrinkersParadox deskolemization" in {

    val ep = ExpansionProof( Sequent() :+ ETWeakQuantifier( hof"?x (P x -> !y (x = x & P y))", Map(
      le"x_0" -> ETImp(
        ETWeakening( hof"P x_0", Negative ),
        ETSkolemQuantifier( hof"!y (x_0 = x_0 & P y)", le"s_0 x_0", le"^x !y (x = x & P y)",
          ETAnd( ETAtom( hoa"x_0 = x_0", Positive ), ETAtom( hoa"P (s_0 x_0)", Positive ) ) ) ),
      le"s_0 x_0" -> ETImp(
        ETAtom( hoa"P (s_0 x_0)", Negative ),
        ETWeakening( hof"!y ((s_0 x_0) = (s_0 x_0) & P y)", Positive ) ) ) ) )
    val desk = deskolemizeET( ep )

    ep.deep must beEValidSequent
    desk.deep must beEValidSequent
    ep.shallow must_== desk.shallow
  }

}
