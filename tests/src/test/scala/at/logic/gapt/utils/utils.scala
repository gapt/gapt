package at.logic.gapt.utils

import at.logic.gapt.expr.{ Expr, Formula }
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.lk.{ CutRule, ForallLeftBlock, LKProof, LogicalAxiom }

object instanceProof {
  def apply( proof: LKProof, terms: List[Expr] ): LKProof = {
    val instantiationFormula = proof.endSequent.succedent.head
    CutRule( proof, instantiationProof( instantiationFormula, terms ), instantiationFormula )
  }

  private def instantiationProof( formula: Formula, terms: List[Expr] ): LKProof = {
    val instanceFormula = instantiate( formula, terms )
    ForallLeftBlock( LogicalAxiom( instanceFormula ), formula, terms )
  }
}

