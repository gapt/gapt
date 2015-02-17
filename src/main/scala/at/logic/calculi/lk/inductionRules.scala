package at.logic.calculi.lk

import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol.HOLConst

object InductionRule {
  def apply( s1: LKProof, s2: LKProof, term1oc: FormulaOccurrence, term2oc: FormulaOccurrence, term3oc: FormulaOccurrence ) = {
    val zero = HOLConst( "0", "i" )
    val succ = HOLConst( "S", "(i -> i)" )

  }

}