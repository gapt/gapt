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
import at.logic.calculi.lksk.lkskExtractors._
import at.logic.calculi.lksk.base._
import at.logic.algorithms.lk.getCutAncestors

import scala.collection.immutable.Set

package struct {
  trait Struct

  case class Times(left: Struct, right: Struct) extends Struct
  case class Plus(left: Struct, right: Struct) extends Struct
  case class Dual(sub: Struct) extends Struct
  case class A(formula: FormulaOccurrence) extends Struct // Atomic Struct
  case class EmptyTimesJunction() extends Struct
  case class EmptyPlusJunction() extends Struct

  object StructCreators {

    def extract(p: LKProof) : Struct = extract( p, getCutAncestors( p ) )

    def extract(p: LKProof, cut_occs: Set[FormulaOccurrence]):Struct = p match {
      case Axiom(so) => // in case of axioms of the form A :- A with labelled formulas, proceed as in Daniel's PhD thesis
      so match {
        case lso : LabelledSequentOccurrence if lso.l_antecedent.size == 1 && lso.l_succedent.size == 1 => {
          val left = lso.l_antecedent.toList.head
          val right = lso.l_succedent.toList.head 
          val ant = if ( cut_occs.contains( left ) )
            Dual( A( new LabelledFormulaOccurrence( left.formula, Nil, right.skolem_label ) ) )::Nil
          else
            Nil
          val suc = if ( cut_occs.contains( right ) )
            A( new LabelledFormulaOccurrence( right.formula, Nil, left.skolem_label ) )::Nil
          else
            Nil
          makeTimesJunction( ant:::suc )
        }
        case _ => {
          val cutAncInAntecedent = so.antecedent.toList.filter(x => cut_occs.contains(x)).map(x => Dual(A(x)))   //
          val cutAncInSuccedent = so.succedent.toList.filter(x => cut_occs.contains(x)).map(x => A(x))
          makeTimesJunction(cutAncInAntecedent:::cutAncInSuccedent)
        }
      }
      case UnaryLKProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
      case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux, _, _) => 
        handleBinary( upperProofLeft, upperProofRight, aux, cut_occs )
      case UnaryLKskProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
    }

    def handleUnary( upperProof: LKProof, cut_occs: Set[FormulaOccurrence] ) =
      extract(upperProof, cut_occs)
    def handleBinary( upperProofLeft: LKProof, upperProofRight: LKProof, aux: FormulaOccurrence,
                      cut_occs: Set[FormulaOccurrence] ) = {
      if (cut_occs.contains(aux)) Plus(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs))
      else Times(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs))
    }

    def makeTimesJunction(structs: List[Struct]):Struct = structs match {
      case Nil => EmptyTimesJunction()
      case s1::Nil => s1
      case s1::tail => Times(s1, makeTimesJunction(tail))
//      case s1::tail => new Times() with Labeled {type T = LKProof, def label: LKProof =  }
    }
  }
}
