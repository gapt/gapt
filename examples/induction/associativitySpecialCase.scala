package gapt.examples.induction
import gapt.expr._
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._
import gapt.provers.spass.SPASS

object associativitySpecialCase extends TacticsProof {
  ctx += InductiveType(ty"nat", hoc"0: nat", hoc"s: nat>nat")
  ctx += hoc"'+': nat>nat>nat"
  ctx += Notation.Infix("+", Precedence.plusMinus)

  def tac = // FIXME(gabriel): WTF, this causes a syntax error when inlined??!?!
    treeGrammarInduction
      .equationalTheory(hof"0+x=x", hof"x+0=x")
      .instanceProver(SPASS.extendToManySortedViaPredicates)
      .quantTys()
      .canSolSize(2)

  val proof = Lemma(
    hols"""p0: !x x+0 = x, ps: !x!y x+s(y) = s(x+y),
           0p: !x 0+x = x, sp: !x!y s(x)+y = s(x+y)
           :- !x (x+x)+x = x+(x+x) """
  ) {
    tac
  }
}
