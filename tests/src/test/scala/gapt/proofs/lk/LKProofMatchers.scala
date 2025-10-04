package gapt.proofs.lk

import gapt.expr.formula.Atom
import gapt.formats.babel.BabelSignature
import gapt.proofs.lk.rules.{EqualityRule, SkolemQuantifierRule}
import gapt.proofs.{Sequent, SequentMatchers}
import org.specs2.matcher.Matchers.pairFunctionToMatcher
import org.specs2.matcher.MustMatchers.theValue
import org.specs2.matcher.{Matcher, Matchers}

trait LKProofMatchers extends Matchers {

  def beSkolemFree: Matcher[LKProof] =
    (actual: LKProof) =>
      (!actual.subProofs.exists(_.isInstanceOf[SkolemQuantifierRule]), "Proof contains skolem inferences")

  def haveAtomicEqualityOnly: Matcher[LKProof] =
    (actual: LKProof) =>
      (
        actual.subProofs
          .filter(_.isInstanceOf[EqualityRule])
          .map(_.asInstanceOf[EqualityRule])
          .forall(e => e.auxFormula.isInstanceOf[Atom]),
        "Proof contains non-atomic equality inferences"
      )

  def beProofOf[A](expected: Sequent[A])(implicit sig: BabelSignature): Matcher[LKProof] = (proof: LKProof) =>
    proof.endSequent must SequentMatchers.beMultiSetEqual(expected)

}
