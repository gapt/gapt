package gapt.examples.tip.prod
import gapt.expr._
import gapt.expr.fol.folTermSize
import gapt.proofs.Context
import gapt.proofs.gaptic._

object prop_31 extends TacticsProof {
  ctx += Ti // TODO(gabriel): support parametrically polymorphic types in TreeGrammarProver
  ctx += Context.InductiveType( ty"list", hoc"nil: list", hoc"cons: i > list > list" )
  ctx += hoc"qrev: list > list > list"

  val revrev = Lemma( hols"""
      qrevnil: !y qrev nil y = y,
      qrevcons: !x!xs!y qrev (cons x xs) y = qrev xs (cons x y)
      :- !x qrev (qrev x nil) nil = x
  """ ) {
    treeGrammarInduction
  }
}