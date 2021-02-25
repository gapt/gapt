package gapt.examples.tip.prod
import gapt.expr._
import gapt.expr.ty.Ti
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object prop_31 extends TacticsProof {
  ctx += Ti // TODO(gabriel): support parametrically polymorphic types in TreeGrammarProver
  ctx += InductiveType( ty"list", hoc"nil: list", hoc"cons: i > list > list" )
  ctx += hoc"qrev: list > list > list"
  val sequent = hols"""
      qrevnil: !y qrev nil y = y,
      qrevcons: !x!xs!y qrev (cons x xs) y = qrev xs (cons x y)
      :- !x qrev (qrev x nil) nil = x
  """
  val revrev = Lemma( sequent ) {
    treeGrammarInduction
  }
}
