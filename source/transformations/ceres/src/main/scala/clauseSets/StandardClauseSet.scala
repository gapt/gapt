/*
 * StandardClauseSet.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.clauseSets

import struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences._
import scala.collection.immutable._

object StandardClauseSet {
  def normalize(struct:Struct):Struct = struct match {
    case Plus(s1,s2) => Plus(normalize(s1), normalize(s2))
    case Times(s1,s2) => merge(normalize(s1), normalize(s2))
    case s: A => s
    case s: Dual => s
    case e: EmptyTimesJunction => e
    case e: EmptyPlusJunction => e
  }

  def transformStructToClauseSet(struct:Struct) = clausify(normalize(struct))

  private def merge(s1:Struct, s2:Struct):Struct = {
    val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))
    val cartesianProduct = for (i <- list1; j <- list2) yield (i,j)
    def transformCartesianProductToStruct(cp: List[Pair[Struct,Struct]]): Struct = cp match {
      case (i,j)::Nil => Times(i, j)
      case (i,j)::rest => Plus(Times(i,j),transformCartesianProductToStruct(rest))
      case Nil => EmptyPlusJunction()
    }
    transformCartesianProductToStruct(cartesianProduct)
  }

  private def getTimesJunctions(struct: Struct):List[Struct] = struct match {
    case s: Times => s::Nil
    case s: EmptyTimesJunction => s::Nil
    case s: A => s::Nil
    case s: Dual => s::Nil
    case s: EmptyPlusJunction => Nil
    case Plus(s1,s2) => getTimesJunctions(s1):::getTimesJunctions(s2)
  }

  private def getLiterals(struct:Struct):List[Struct] = struct match {
    case s: A => s::Nil
    case s: Dual => s::Nil
    case s: EmptyTimesJunction => Nil
    case s: EmptyPlusJunction => Nil
    case Plus(s1,s2) => getLiterals(s1):::getLiterals(s2)
    case Times(s1,s2) => getLiterals(s1):::getLiterals(s2)
  }

  private def clausifyTimesJunctions(struct: Struct): SequentOccurrence = {
    def isDual(s:Struct):Boolean = s match {case x: Dual => true; case _ => false}
    val literals = getLiterals(struct)
    val (negative,positive) = literals.partition(x => isDual(x))
    val negativeFO: List[FormulaOccurrence] = negative.map(x => x.asInstanceOf[Dual].sub.asInstanceOf[A].fo) // extracting the formula occurrences from the negative literal structs
    val positiveFO: List[FormulaOccurrence] = positive.map(x => x.asInstanceOf[A].fo)     // extracting the formula occurrences from the positive atomic struct
    def convertListToSet[T](list:List[T]):Set[T] = list match {
      case x::rest => convertListToSet(rest)+x
      case Nil => new HashSet[T]
    }
    val negativeFOSet = convertListToSet(negativeFO)
    val positiveFOSet = convertListToSet(positiveFO)
    SequentOccurrence(negativeFOSet,positiveFOSet)
  }

  def clausify(struct: Struct): List[SequentOccurrence] = {
    val timesJunctions = getTimesJunctions(struct)
    timesJunctions.map(x => clausifyTimesJunctions(x))
  }
}
