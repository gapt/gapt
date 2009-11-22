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
case class A(fo: FormulaOccurrence) extends Struct // Atomic Struct
case class EmptyTimesJunction() extends Struct
case class EmptyPlusJunction() extends Struct

object StructCreators {

  def extract(p: LKProof):Struct = p match {
    case Axiom(so) => {
      val cutAncInAntecedent = so.antecedent.toList.filter(x => isCutAncestor(x,p)).map(x => Dual(A(x)))   //
      val cutAncInSuccedent = so.succedent.toList.filter(x => isCutAncestor(x,p)).map(x => A(x))
      makeTimesJunction(cutAncInAntecedent:::cutAncInSuccedent)
    }
    case UnaryLKProof(_,upperProof,_,_,_) => extract(upperProof)
    case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) => {
      if (isCutAncestor(aux1,p)) Plus(extract(upperProofLeft), extract(upperProofRight))
      else Times(extract(upperProofLeft), extract(upperProofRight))
    }
  }

  def makeTimesJunction(structs: List[Struct]):Struct = structs match {
    case Nil => EmptyTimesJunction()
    case s1::Nil => s1
    case s1::tail => Times(s1, makeTimesJunction(tail))
  }

  def isCutAncestor(fo: FormulaOccurrence, p: LKProof):Boolean = {
    try {
      p.getDescendantInLowerSequent(fo: FormulaOccurrence) 
    } catch {
      case e: FormulaNotExistsException => return true
    }
    return false
  }
}
