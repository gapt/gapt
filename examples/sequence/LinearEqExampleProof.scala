package gapt.examples.sequence

import gapt.expr._
import gapt.expr.Expr
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.repeat

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * Refl, Trans, \ALL x. f(x) = x :- f^n^(a) = a
 *
 * where n is an Integer parameter >= 0.
 */
object LinearEqExampleProof extends TacticsProof with ProofSequence with ExplicitEqualityTactics {
  ctx += Sort("i")
  ctx += hoc"f: i>i"
  ctx += hoc"a: i"

  // f^k(a)
  private def fk(k: Int): Expr =
    LazyList.iterate(le"a")(x => le"f $x")(k)

  def apply(n: Int) =
    Proof(
      ("refl" -> hof"∀(x:i) x=x") +:
        ("trans" -> hof"∀(x:i)∀y∀z (x=y ∧ y=z → x=z)") +:
        ("id" -> hof"∀x f(x)=x") +: Sequent()
        :+ ("goal" -> hof"${fk(n)} = a")
    ) {
      repeat(explicitRewriteLeft("id", "goal"))
      chain("refl")
    }
}
