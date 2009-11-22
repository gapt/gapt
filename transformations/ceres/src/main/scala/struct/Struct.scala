/*
 * Struct.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package struct

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk._
import at.logic.calculi.lk.propositionalRules._

trait Struct

case class Times(left: Struct, right: Struct) extends Struct
case class Plus(left: Struct, right: Struct) extends Struct
case class Dual(sub: Struct) extends Struct
case class Atom(exp: LambdaExpression)

object StructCreators {

  def extract(p: LKProof) = false //ToDo

  def isCutAncestor(fo: FormulaOccurrence, p: LKProof):Boolean = {
    try {
      p.getDescendantInLowerSequent(fo: FormulaOccurrence) 
    } catch {
      case e: FormulaNotExistsException => return true
    }
    return false
  }

}
