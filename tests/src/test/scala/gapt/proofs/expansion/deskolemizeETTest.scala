package gapt.proofs.expansion

import gapt.examples.CountingEquivalence
import gapt.logic.Polarity.{Negative, Positive}
import gapt.expr._
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.provers.escargot.Escargot
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class deskolemizeETTest extends Specification with SatMatchers {

  "DrinkersParadox deskolemization" in {

    val ep = ExpansionProof(Sequent() :+ ETWeakQuantifier(
      hof"?x (P x -> !y (x = x & P y))",
      Map(
        le"x_0" -> ETImp(
          ETWeakening(hof"P x_0", Negative),
          ETSkolemQuantifier(hof"!y (x_0 = x_0 & P y)", le"s_0 x_0", ETAnd(ETAtom(hoa"x_0 = x_0", Positive), ETAtom(hoa"P (s_0 x_0)", Positive)))
        ),
        le"s_0 x_0" -> ETImp(
          ETAtom(hoa"P (s_0 x_0)", Negative),
          ETWeakening(hof"!y ((s_0 x_0) = (s_0 x_0) & P y)", Positive)
        )
      )
    ))
    val desk = deskolemizeET(ep)

    ep.deep must beEValidSequent
    desk.deep must beEValidSequent
    ep.shallow must_== desk.shallow
  }

  "drinker" in {
    val Some(drinker) = Escargot.getExpansionProof(hof"?x (p(x) -> !y p(y))"): @unchecked
    val deskolemized = deskolemizeET(drinker)
    deskolemized.deep must beValidSequent
    deskolemized.shallow must_== drinker.shallow
  }

  "drinker 2" in {
    val drinker = ExpansionProof(Sequent() :+
      ExpansionTree(hof"∃x (p(x) -> ∀y p(y))", Polarity.InSuccedent, ETtWeak(le"f" -> ETtBinary(ETtAtom, ETtSkolem(le"f", ETtAtom)))))
    drinker.deep must beValidSequent
    val deskolemized = deskolemizeET(drinker)
    deskolemized.deep must beValidSequent
    deskolemized.shallow must_== drinker.shallow
  }

  "counting 0" in {
    val Some(proof) = Escargot.getExpansionProof(CountingEquivalence(0)): @unchecked
    val deskolemized = deskolemizeET(proof)
    deskolemized.deep must beValidSequent
    deskolemized.shallow must_== proof.shallow
  }

  "counting 1" in {
    val Some(proof) = Escargot.getExpansionProof(CountingEquivalence(1)): @unchecked
    val deskolemized = deskolemizeET(proof)
    deskolemized.deep must beValidSequent
    deskolemized.shallow must_== proof.shallow
  }

  "quantifier shifting" in {
    val Some(proof) = Escargot.getExpansionProof(hof"!x?y!z?w P(x,y,z,w) -> !x!z?y?w P(x,y,z,w)"): @unchecked
    val deskolemized = deskolemizeET(proof)
    deskolemized.deep must beValidSequent
    deskolemized.shallow must_== proof.shallow
  }

}
