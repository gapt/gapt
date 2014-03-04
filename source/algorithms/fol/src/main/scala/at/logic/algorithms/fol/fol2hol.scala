package at.logic.algorithms.fol

import at.logic.language.fol.{FOLVar, FOLFormula, FOLExpression}
import at.logic.language.hol._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.base.types.FSequent

/**
 * Sometimes it is necessary to convert terms to an upper layer: e.g. applying a fol subtitution to a hol term does not
 * work if the result is not first order.
 */
object fol2hol {
  def apply(e:FOLExpression) : HOLExpression = e match {
    case HOLVar(sym, t) => HOLVar(sym,t)
    case HOLApp(s,t) => HOLApp(s,t)
    case HOLAbs(x,t) => HOLAbs(x,t)
    case _ => throw new Exception("Could not convert fol term "+e+" to hol!")
  }

  def apply(f:FOLFormula) : HOLFormula = fol2hol(f.asInstanceOf[FOLExpression]).asInstanceOf[HOLFormula]

  def apply(f:FSequent) : FSequent =
    FSequent(f.antecedent.map(_ match {
      case folf: FOLFormula => fol2hol(folf)
      case holf: HOLFormula => holf
    }), f.succedent.map(_ match {
      case folf: FOLFormula => fol2hol(folf)
      case holf: HOLFormula => holf
    }))

  def apply(sub: Substitution[FOLExpression]) : Substitution[HOLExpression] = Substitution[HOLExpression](sub.map.map(x=>
      (fol2hol(x._1.asInstanceOf[FOLVar]).asInstanceOf[Var], fol2hol(x._2)) ))
}
