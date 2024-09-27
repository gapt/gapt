package gapt.proofs.lk.rules

import gapt.expr.{BetaReduction, Expr, Var}
import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

abstract class WeakQuantifierRule extends UnaryLKProof with CommonRule {
  val aux: SequentIndex
  val A: Formula
  val term: Expr
  val v: Var

  def auxFormula: Formula = premise(aux)
  if (auxFormula != BetaReduction.betaNormalize(Substitution(v, term)(A)))
    throw LKRuleCreationException(s"Substituting $term for $v in $A does not result in ${premise(aux)}.")

  def mainFormula: Formula
}

object WeakQuantifierRule {
  def apply(p: LKProof, aux: SequentIndex, f: Formula, t: Expr, v: Var, isExists: Boolean): WeakQuantifierRule =
    if (isExists)
      ExistsRightRule(p, aux, f, t, v)
    else
      ForallLeftRule(p, aux, f, t, v)

  def apply(p: LKProof, main: Formula, t: Expr, isExists: Boolean): WeakQuantifierRule =
    if (isExists)
      ExistsRightRule(p, main, t)
    else
      ForallLeftRule(p, main, t)

  def unapply(p: WeakQuantifierRule): Option[(LKProof, SequentIndex, Formula, Expr, Var, Boolean)] = p match {
    case ForallLeftRule(subProof, aux, f, t, v) =>
      Some((subProof, aux, f, t, v, false))
    case ExistsRightRule(subProof, aux, f, t, v) =>
      Some((subProof, aux, f, t, v, true))
    case _ => None
  }
}
