package at.logic.algorithms.resolution

/**
 * Created with IntelliJ IDEA.
 * User: shaolin
 * Date: 8/17/12
 * Time: 4:06 PM
 * To change this template use File | Settings | File Templates.
 */

import at.logic.calculi.lk.base.types._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.equationalRules.{EquationRight2Rule, EquationRight1Rule, EquationLeft2Rule, EquationLeft1Rule}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol.{Equation, FOLTerm, FOLFormula, FOLExpression}
import at.logic.language.hol._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{Var, App}
import at.logic.calculi.resolution.base.Clause
import collection.immutable.HashSet

object RobinsonToLK {
  def apply(resproof: RobinsonResolutionProof): LKProof = recConvert(resproof, Substitution[FOLExpression]())

  // sub is the aggregated substitution in the resolution proof which must be applied to the lk proof,
  // do we need to ground free variables as well?
  private def recConvert(proof: RobinsonResolutionProof, sub: Substitution[FOLExpression]): LKProof = proof match {
    case InitialClause(cls) => Axiom(cls.negative.map(fo => sub(fo.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]), cls.positive.map(fo => sub(fo.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]))
    case Factor(r, p, a, s) => {
      // obtain the set of removed occurrences for each side
      val leftSet = r.antecedent.map(_.formula)
      val leftContracted = p.root.antecedent.filterNot(fo => leftSet.contains(fo.formula))
      val rightSet = r.succedent.map(_.formula)
      val rightContracted = p.root.succedent.filterNot(fo => rightSet.contains(fo.formula))
      // obtain upper proof recursively
      val curSub = sub.compose(s)
      var res = recConvert(p, curSub)
      // create a contraction for each side, for each contracted formula with a._1 and a._2 (if exists)
      // note that sub must be applied to all formulas in the lk proof
      // var hasLeft = false
      if (!leftContracted.isEmpty) {
        // val leftAux = a(0) since we do not compare occurrences but only formulas and all formulas are identical in LK contraction, we can ignore this value
        // hasLeft = true
        res = leftContracted.foldLeft(res)((p, fo) => ContractionLeftRule(p, curSub(fo.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]))
      }
      if (!rightContracted.isEmpty) {
        // val rightAux = if (hasLeft) a(1) else a(0)
        res = rightContracted.foldLeft(res)((p, fo) => ContractionRightRule(p, curSub(fo.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]))
      }
      res
    }
    case Variant(r, p, s) => recConvert(p, sub.compose(s)) // the construction of an LK proof makes sure we create a tree out of the agraph
    case Resolution(r, p1, p2, a1, a2, s) => {
      val curSub = sub.compose(s)
      val u1: LKProof = recConvert(p1, curSub)
      val u2: LKProof = recConvert(p2, curSub)

      CutRule(u1, u2, curSub(a1.formula.asInstanceOf[FOLFormula]).asInstanceOf[FOLFormula])
    }
    case Paramodulation(r, p1, p2, a1, a2, s) => {
      val curSub = sub.compose(s)
      val u1 = recConvert(p1, curSub)
      val u2 = recConvert(p2, curSub)
      val Atom(_, s0 :: _) = a1.formula
      val s1 = curSub(s0.asInstanceOf[FOLExpression]).asInstanceOf[FOLTerm]
      // locate principal formula
      val lo = r.antecedent.find(_.ancestors.contains(a2))
      val ro = r.succedent.find(_.ancestors.contains(a2))
      // left rule
      if (ro == None) {
        val lof = lo.get.formula.asInstanceOf[FOLFormula]
        // locate aux formulae
        val aux1 = u1.root.succedent.find(_.formula == curSub(a1.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
        val aux2 = u2.root.antecedent.find(_.formula == curSub(a2.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
        // rule 1
        if (isRule1(lof, aux2.formula.asInstanceOf[FOLFormula], s1)) EquationLeft1Rule(u1, u2, aux1, aux2, lof)
        // rule 2
        else EquationLeft2Rule(u1, u2, aux1, aux2, lof)
      }
      // right rule
      else {
        val rof = ro.get.formula.asInstanceOf[FOLFormula]
        // locate aux formulae
        val aux1 = u1.root.succedent.find(_.formula == curSub(a1.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
        val aux2 = u2.root.succedent.find(_.formula == curSub(a2.formula.asInstanceOf[FOLExpression]).asInstanceOf[FOLFormula]).get
        // rule 1
        if (isRule1(rof, aux2.formula.asInstanceOf[FOLFormula], s1)) EquationRight1Rule(u1, u2, aux1, aux2, rof)
        // rule 2
        else EquationRight2Rule(u1, u2, aux1, aux2, rof)
      }
    }
  }

  // in order to distinguish between rule 1 and rule 2 in equation rules we search for the substituted formula in the obtained one
  // if f2 contains more occurrences of the sub term than f1 then it means that this subterm was replaced by something else
  private def isRule1(f1: FOLFormula, f2: FOLFormula, t: FOLTerm): Boolean = (countSB(f2, t) > countSB(f1, t))

  private def countSB(t1: HOLExpression, t2: HOLExpression): Int =
    if (t1 == t2) 1
    else t1 match {
      case Var(_, _) => 0
      case Atom(_, args) => args.foldLeft(0)((n, arg) => n + countSB(arg, t2))
      case Function(_, args, _) => args.foldLeft(0)((n, arg) => n + countSB(arg, t2))
    }
}