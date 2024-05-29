package gapt.proofs.expansion
import gapt.expr._
import gapt.logic.Polarity.{InSuccedent, InAntecedent}
import gapt.proofs.Sequent
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class RemoveSkolemCongruencesTest extends Specification with SatMatchers {

  def desk(ep: ExpansionProof): ExpansionProof =
    deskolemizeET.replaceByEigenvariables(ep)

  "simple" in {
    val ep = ExpansionProof(
      ETAtom(hoa"a=b", InAntecedent) +:
        ExpansionTree(
          hof"!x?y P(x,y)",
          InAntecedent,
          ETtWeak(le"a" ->
            ETtSkolem(le"f a", ETtAtom))
        ) +:
        Sequent() :+
        ExpansionTree(hof"?x P(b,x)", InSuccedent, ETtWeak(le"f b" -> ETtAtom))
    )
    ep.deep must beEValidSequent
    desk(ep).deep must not(beEValidSequent)
    val ep2 = removeSkolemCongruences(ep)
    desk(ep2).deep must beEValidSequent
  }

  "block" in {
    val ep = ExpansionProof(
      ETAtom(hoa"a=b", InAntecedent) +:
        ETAtom(hoa"b=c", InAntecedent) +:
        ExpansionTree(hof"!x?y?z P(x,y,z)", InAntecedent, ETtWeak(le"a" -> ETtSkolem(le"f a", ETtSkolem(le"g a", ETtAtom)))) +:
        Sequent() :+
        ExpansionTree(hof"?x?y P(b,x,y)", InSuccedent, ETtWeak(le"f b" -> ETtWeak(le"g c" -> ETtAtom)))
    )
    ep.deep must beEValidSequent
    desk(ep).deep must not(beEValidSequent)
    val ep2 = removeSkolemCongruences(ep)
    desk(ep2).deep must beEValidSequent
  }

}
