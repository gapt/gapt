package at.logic.calculi.slk

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/16/11
 * Time: 5:30 PM
 */

package macroRules {

import at.logic.calculi.lk.base.{LKRuleCreationException, LKProof}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.schema._
import at.logic.calculi.slk._

object AndEquivalenceRule {
    def apply(p: LKProof, auxf: FormulaOccurrence, main: SchemaFormula) = {
      main match {
        case BigAnd(v, f, ub, Succ(lb))
          if And( BigAnd( v, f, ub, lb ), betaNormalize( App(Abs(v, f), Succ(lb)) ).asInstanceOf[SchemaFormula] ) == auxf.formula =>
          AndEquivalenceRule1(p, auxf, main)
        case BigAnd(v, f, ub, lb)
          if And( BigAnd( v, f, Succ(ub), lb ), betaNormalize( App(Abs(v, f), ub) ).asInstanceOf[SchemaFormula] ) == auxf.formula =>
          AndEquivalenceRule2(p, auxf, main)
        case BigAnd(v, f, ub, lb) if ub == lb => AndEquivalenceRule3(p, auxf, main)
        case _ => throw new LKRuleCreationException("Main formula of AndEquivalenceRule must have a BigAnd as head symbol.")
      }
    }
  }

}