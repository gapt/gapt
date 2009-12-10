/*
 * Struct.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.ceres

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.lkExtractors._
import at.logic.language.hol.propositions.Formula

import scala.collection.immutable.Set

package struct {
  trait Struct

  case class Times(left: Struct, right: Struct) extends Struct
  case class Plus(left: Struct, right: Struct) extends Struct
  case class Dual(sub: Struct) extends Struct
  case class A(formula: Formula) extends Struct // Atomic Struct
  case class EmptyTimesJunction() extends Struct
  case class EmptyPlusJunction() extends Struct

  object StructCreators {

    def extract(p: LKProof, cut_occs: Set[FormulaOccurrence]):Struct = p match {
      case Axiom(so) => {
        val cutAncInAntecedent = so.antecedent.toList.filter(x => cut_occs.contains(x)).map(x => Dual(A(x.formula)))   //
        val cutAncInSuccedent = so.succedent.toList.filter(x => cut_occs.contains(x)).map(x => A(x.formula))
        makeTimesJunction(cutAncInAntecedent:::cutAncInSuccedent)
      }
      case UnaryLKProof(_,upperProof,_,_,_) => extract(upperProof, cut_occs)
      case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) => {
        if (cut_occs.contains(aux1)) Plus(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs))
        else Times(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs))
      }
    }

    def makeTimesJunction(structs: List[Struct]):Struct = structs match {
      case Nil => EmptyTimesJunction()
      case s1::Nil => s1
      case s1::tail => Times(s1, makeTimesJunction(tail))
    }
  }
}
