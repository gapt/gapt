package at.logic.language.fol.replacements

import at.logic.language.hol
import at.logic.language.fol.FOLExpression

/**
 * Created by cthulhu on 18.06.14.
 */

object getAtPositionFOL {
  def apply(expression: FOLExpression, pos: List[Int]): FOLExpression = hol.replacements.getAtPosition(expression,pos).asInstanceOf[FOLExpression]
}

object getAllPositionsFOL {
  def apply(expression: FOLExpression): List[Tuple2[List[Int], FOLExpression]] = hol.replacements.getAllPositions(expression.asInstanceOf[hol.HOLExpression]).asInstanceOf[List[Tuple2[List[Int],FOLExpression]]]
}