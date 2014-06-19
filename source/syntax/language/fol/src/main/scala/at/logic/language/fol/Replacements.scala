package at.logic.language.fol.replacements

import at.logic.language.hol
import at.logic.language.fol.FOLExpression
import at.logic.language.hol.HOLExpression

/**
 * Created by cthulhu on 18.06.14.
 */

object getAtPositionFOL {
  def apply(expression: FOLExpression, pos: List[Int]): FOLExpression = hol.replacements.getAtPosition(expression,pos).asInstanceOf[FOLExpression]
}

object getAllPositionsFOL {
  def apply(expression: FOLExpression): List[Tuple2[List[Int], FOLExpression]] = hol.replacements.getAllPositions(expression.asInstanceOf[hol.HOLExpression]).asInstanceOf[List[Tuple2[List[Int],FOLExpression]]]
}

class Replacement(position: List[Int], expression: FOLExpression) extends hol.replacements.Replacement(position,expression) {
  def apply(exp: FOLExpression) : FOLExpression = super.apply(exp.asInstanceOf[HOLExpression]).asInstanceOf[FOLExpression]
}