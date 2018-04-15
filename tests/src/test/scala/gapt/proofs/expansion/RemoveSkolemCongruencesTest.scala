package gapt.proofs.expansion
import gapt.expr._
import Polarity._
import gapt.proofs.Sequent
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class RemoveSkolemCongruencesTest extends Specification with SatMatchers {

  def desk( ep: ExpansionProof ): ExpansionProof =
    deskolemizeET.replaceByEigenvariables( ep )

  "simple" in {
    val ep = ExpansionProof(
      ETAtom( hoa"a=b", InAntecedent ) +:
        ETWeakQuantifier( hof"!x?y P(x,y)", Map( le"a" ->
          ETSkolemQuantifier( hof"?y P(a,y)", le"f a", le"^x?y P(x,y)",
            ETAtom( hoa"P(a,f a)", InAntecedent ) ) ) ) +:
        Sequent() :+
        ETWeakQuantifier( hof"?x P(b,x)", Map( le"f b" -> ETAtom( hoa"P(b, f b)", InSuccedent ) ) ) )
    ep.deep must beEValidSequent
    desk( ep ).deep must not( beEValidSequent )
    val ep2 = removeSkolemCongruences( ep )
    desk( ep2 ).deep must beEValidSequent
  }

  "block" in {
    val ep = ExpansionProof(
      ETAtom( hoa"a=b", InAntecedent ) +:
        ETAtom( hoa"b=c", InAntecedent ) +:
        ETWeakQuantifier( hof"!x?y?z P(x,y,z)", Map( le"a" ->
          ETSkolemQuantifier( hof"?y?z P(a,y,z)", le"f a", le"^x?y?z P(x,y,z)",
            ETSkolemQuantifier( hof"?z P(a,f a,z)", le"g a", le"^x?z P(x,f x,z)",
              ETAtom( hoa"P(a,f a,g a)", InAntecedent ) ) ) ) ) +:
        Sequent() :+
        ETWeakQuantifier( hof"?x?y P(b,x,y)", Map( le"f b" ->
          ETWeakQuantifier( hof"?y P(b, f b, y)", Map( le"g c" ->
            ETAtom( hoa"P(b, f b, g c)", InSuccedent ) ) ) ) ) )
    ep.deep must beEValidSequent
    desk( ep ).deep must not( beEValidSequent )
    val ep2 = removeSkolemCongruences( ep )
    desk( ep2 ).deep must beEValidSequent
  }

}
