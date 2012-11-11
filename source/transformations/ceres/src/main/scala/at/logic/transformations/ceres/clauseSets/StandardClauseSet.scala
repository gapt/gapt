/*
 * StandardClauseSet.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.ceres.clauseSets

import at.logic.transformations.ceres.struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
import at.logic.language.schema.IndexedPredicate
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.types.{To, Tindex}
import at.logic.language.hol.{HOLApp, HOLConst, HOLFormula}
import types.FSequent

object StandardClauseSet {
  def normalize(struct:Struct):Struct = struct match {
    case Plus(s1,s2) => Plus(normalize(s1), normalize(s2))
    case Times(s1,s2,aux) => merge(normalize(s1), normalize(s2),aux)
    case s: A => s
    case s: Dual => s
    case e: EmptyTimesJunction => e
    case e: EmptyPlusJunction => e
  }

  def transformStructToClauseSet(struct:Struct) = clausify(normalize(struct))

  def transformStructToLabelledClauseSet(struct:Struct) =
    transformStructToClauseSet(struct).map( so => sequentToLabelledSequent( so ) )

  private def merge(s1:Struct, s2:Struct, aux: List[FormulaOccurrence]):Struct = {
    val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))
    val cartesianProduct = for (i <- list1; j <- list2) yield (i,j)
    def transformCartesianProductToStruct(cp: List[Pair[Struct,Struct]]): Struct = cp match {
      case (i,j)::Nil => Times(i, j, aux)
      case (i,j)::rest => Plus(Times(i,j, aux),transformCartesianProductToStruct(rest))
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
    case Times(s1,s2,_) => getLiterals(s1):::getLiterals(s2)
  }

  private def clausifyTimesJunctions(struct: Struct): Sequent = {
    def isDual(s:Struct):Boolean = s match {case x: Dual => true; case _ => false}
    val literals = getLiterals(struct)
    val (negative,positive) = literals.partition(x => isDual(x))
    val negativeFO: Seq[FormulaOccurrence] = negative.map(x => x.asInstanceOf[Dual].sub.asInstanceOf[A].fo) // extracting the formula occurrences from the negative literal structs
    val positiveFO: Seq[FormulaOccurrence] = positive.map(x => x.asInstanceOf[A].fo)     // extracting the formula occurrences from the positive atomic struct
    def convertListToSet[T](list:List[T]):Set[T] = list match {
      case x::rest => convertListToSet(rest)+x
      case Nil => new HashSet[T]
    }
    Sequent(negativeFO, positiveFO)
  }

  def clausify(struct: Struct): List[Sequent] = {
    val timesJunctions = getTimesJunctions(struct)
    timesJunctions.map(x => clausifyTimesJunctions(x))
  }
}

object renameCLsymbols {
  def createMap(cs: List[Sequent]): Map[HOLConst, String] = {
    var i: Int = 1
    var map = Map.empty[HOLConst, String]
    cs.foreach(seq => {
      (seq.antecedent ++ seq.succedent).foreach(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if (constant.name.isInstanceOf[ClauseSetSymbol]) => {
            if (!map.contains(constant)) {
              map = map + Pair(constant, i.toString)
              i = i + 1
            }
          }
          case _ => {}
        }
      })
    })
    return map
  }
  
  def apply(cs: List[Sequent]): List[FSequent] = {
    val map = createMap(cs)
    cs.map(seq => {
      val ant = seq.antecedent.map(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if (constant.name.isInstanceOf[ClauseSetSymbol]) => {
            if (map.contains(constant)) {
              val c = HOLConst(new ConstantStringSymbol("CL"+map.get(constant).get), Tindex()->To())
              HOLApp(c, indices.head)
            }
            else
              throw new Exception("\nError in renameCLsymbols.apply !\n")
          }
          case _ => fo.formula
        }
      })
      val succ = seq.succedent.map(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if (constant.name.isInstanceOf[ClauseSetSymbol]) => {
            if (map.contains(constant)) {
              val c = HOLConst(new ConstantStringSymbol("CL"+map.get(constant).get), Tindex()->To())
              HOLApp(c, indices.head)
            }
            else
              throw new Exception("\nError in renameCLsymbols.apply !\n")
          }
          case _ => fo.formula
        }
      })
      FSequent(ant.asInstanceOf[List[HOLFormula]], succ.asInstanceOf[List[HOLFormula]])
    })
  }
}