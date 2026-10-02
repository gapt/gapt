package gapt.proofs.lk.transformations

import gapt.expr.stringInterpolationForExpressions
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.{AndLeftRule, AndRightRule, ContractionLeftRule, ContractionRightRule, CutRule, LogicalAxiom, NegLeftRule, WeakeningLeftRule, WeakeningRightRule}
import org.specs2.mutable.Specification

class cleanStructuralRulesTest extends Specification {
  private val atom = hof"P"
  private val q = hof"Q"
  private val r = hof"R"
  private val ax = LogicalAxiom(atom)

  private def clean(proof: LKProof, reductive: Boolean = true): LKProof = {
    val (cleaned, connector) = cleanStructuralRules.withSequentConnector(proof, reductive)
    assert(cleaned.endSequent.sizes == proof.endSequent.sizes)
    assert(cleaned.endSequent.diff(proof.endSequent).isEmpty)
    for (i <- proof.endSequent.indices) {
      assert(connector.children(i).nonEmpty)
      assert(connector.children(i).forall(j => cleaned.endSequent(j) == proof.endSequent(i)))
    }
    cleaned
  }

  "cleanStructuralRules" should {
    "preserve initial sequents" in {
      clean(ax) must_== ax
    }

    "discard contractions with weak auxiliary occurrences on either side" in {
      val left = ContractionLeftRule(WeakeningLeftRule(ax, atom), atom)
      val proof = ContractionRightRule(WeakeningRightRule(left, atom), atom)
      clean(proof) must_== ax
    }

    "replace an inference on a weak formula with a final weakening" in {
      val proof = NegLeftRule(WeakeningRightRule(ax, q), q)
      clean(proof) must_== WeakeningLeftRule(ax, -q)
    }

    "restore a weak conjunct while moving unrelated weakenings downward" in {
      val proof = AndLeftRule(WeakeningLeftRule(WeakeningLeftRule(ax, r), q), atom, q)
      val expected = WeakeningLeftRule(AndLeftRule(WeakeningLeftRule(ax, q), atom, q), r)
      clean(proof) must_== expected
    }

    "discard the unused side of a cut in reductive mode" in {
      val proof = CutRule(WeakeningRightRule(ax, q), LogicalAxiom(q), q)
      clean(proof) must_== WeakeningRightRule(ax, q)
    }

    "retain cuts in non-reductive mode" in {
      val proof = CutRule(WeakeningRightRule(ax, q), LogicalAxiom(q), q)
      clean(proof, reductive = false) must_== proof
    }

    "discard a binary inference with a weak auxiliary formula in reductive mode" in {
      val proof = AndRightRule(WeakeningRightRule(ax, q), q, LogicalAxiom(r), r)
      val expected = WeakeningRightRule(WeakeningLeftRule(ax, r), q & r)
      clean(proof) must_== expected
    }

    "retain both sides of a binary inference in non-reductive mode" in {
      val proof = AndRightRule(WeakeningRightRule(ax, q), q, LogicalAxiom(r), r)
      clean(proof, reductive = false) must_== proof
    }
  }
}
