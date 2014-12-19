package at.logic.language.fol.replacements

import at.logic.language.hol
import at.logic.language.fol.FOLExpression
import at.logic.language.hol.HOLExpression

/**
 * Created by cthulhu on 18.06.14.
 */


/**
 * Returns a specific subterm within a position.
 *
 * This is a wrapper around the hol version.
 */
object getAtPositionFOL {
  /**
   * Returns the subterm at expression | pos
   * @param expression An arbitrary hol expression
   * @param pos A path of branchings in the term tree. Nil is the root position, 1 is the first argument  etc.
   * @return The subterm, if it exists.
   */
  def apply(expression: FOLExpression, pos: List[Int]): FOLExpression = hol.replacements.getAtPosition(expression,pos).asInstanceOf[FOLExpression]
}

/**
 * Calculates a list of all subterms of an expression together with their respective positions.
 *
 * This is a wrapper around hol's getAllPositions2.
 */
object getAllPositionsFOL {
  /**
   * Calculates a list of all subterms of an expression together with their respective positions.
   * @param expression an arbitrary hol epxression
   * @return a list of pairs (position, subterm)
   */
  def apply(expression: FOLExpression): List[Tuple2[List[Int], FOLExpression]] = hol.replacements.getAllPositions2(expression.asInstanceOf[hol.HOLExpression]).asInstanceOf[List[Tuple2[List[Int],FOLExpression]]]
}

/**
 * Replacement represents the rewriting notion of a hole at a certain position. We expect that
 * the passed expression will replace the subterm indicated at the given position. Positions are
 * denoted like in term rewriting.
 *
 * This is a wrapper around the hol Replacement class.
 * @example {{{
 *          val expr = And(Atom("P", List(FOLConst("a"), FOLConst("b"))), Atom("Q", Nil))
 *          val f = Replacement(List(1,2), FOLVar("x" ))(expr)
 *          f == And(Atom("P", List(FOLConst("a"), FOLVar("x"))), Atom("Q", Nil))
 *          }}}
 *
 * @param position A path of branchings in the term tree. Nil is the root position, 1 is the first argument  etc.
 * @param expression The term which will be inserted.
 */
class Replacement(position: List[Int], expression: FOLExpression) extends hol.replacements.Replacement(position,expression) {
  def apply(exp: FOLExpression) : FOLExpression = super.apply(exp.asInstanceOf[HOLExpression]).asInstanceOf[FOLExpression]
}