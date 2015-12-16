package at.logic.gapt.proofs.shlk

import at.logic.gapt.proofs.lkOld.base.{ LKRuleCreationException, LKProof }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.expr._
import at.logic.gapt.expr.schema._
import BetaReduction._

object AndEquivalenceRule {
  def apply( p: LKProof, auxf: FormulaOccurrence, main: SchemaFormula ) = {
    main match {
      case BigAnd( v, f, ub, Succ( lb ) ) if And( BigAnd( v, f, ub, lb ), betaNormalize( App( Abs( v, f ), Succ( lb ) ) ).asInstanceOf[SchemaFormula] ) == auxf.formula =>
        AndEquivalenceRule1( p, auxf, main )
      case BigAnd( v, f, ub, lb ) if And( BigAnd( v, f, Succ( ub ), lb ), betaNormalize( App( Abs( v, f ), ub ) ).asInstanceOf[SchemaFormula] ) == auxf.formula =>
        AndEquivalenceRule2( p, auxf, main )
      case BigAnd( v, f, ub, lb ) if ub == lb => AndEquivalenceRule3( p, auxf, main )
      case _                                  => throw new LKRuleCreationException( "Main formula of AndEquivalenceRule must have a BigAnd as head symbol." )
    }
  }
}

