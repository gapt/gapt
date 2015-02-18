package at.logic.gapt.proofs.shlk

import at.logic.gapt.proofs.lk.base.{ LKRuleCreationException, LKProof }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
//import at.logic.gapt.language.lambda.typedLambdaCalculus.{App, Abs}
//import at.logic.gapt.language.lambda.BetaReduction._
//import at.logic.gapt.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.gapt.language.schema._
import at.logic.gapt.language.schema.BetaReduction._
//import at.logic.calculi.slk._

object AndEquivalenceRule {
  def apply( p: LKProof, auxf: FormulaOccurrence, main: SchemaFormula ) = {
    main match {
      case BigAnd( v, f, ub, Succ( lb ) ) if SchemaAnd( BigAnd( v, f, ub, lb ), betaNormalize( SchemaApp( SchemaAbs( v, f ), Succ( lb ) ) ).asInstanceOf[SchemaFormula] ) == auxf.formula =>
        AndEquivalenceRule1( p, auxf, main )
      case BigAnd( v, f, ub, lb ) if SchemaAnd( BigAnd( v, f, Succ( ub ), lb ), betaNormalize( SchemaApp( SchemaAbs( v, f ), ub ) ).asInstanceOf[SchemaFormula] ) == auxf.formula =>
        AndEquivalenceRule2( p, auxf, main )
      case BigAnd( v, f, ub, lb ) if ub == lb => AndEquivalenceRule3( p, auxf, main )
      case _                                  => throw new LKRuleCreationException( "Main formula of AndEquivalenceRule must have a BigAnd as head symbol." )
    }
  }
}

