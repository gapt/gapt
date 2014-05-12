/*
 * StandardClauseSet.scala
 *
 */

package at.logic.transformations.ceres.clauseSets

import at.logic.transformations.ceres.struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk._
import at.logic.calculi.occurrences._
import at.logic.language.schema.IndexedPredicate
import at.logic.language.lambda.types.{To, Tindex}
import at.logic.language.hol.{HOLExpression, HOLApp, HOLConst, HOLFormula}
import scala.collection.immutable.HashSet
import scala.annotation.tailrec

object StandardClauseSet {
  def normalize(struct:Struct):Struct = struct match {
    case s: A => s
    case s: Dual => s
    case e: EmptyTimesJunction => e
    case e: EmptyPlusJunction => e
    case Plus(s1,s2) => Plus(normalize(s1), normalize(s2))
    case Times(s1,s2,aux) => merge(normalize(s1), normalize(s2),aux)
  }

  def transformStructToClauseSet(struct:Struct) = clausify(normalize(struct))

  def transformStructToLabelledClauseSet(struct:Struct) =
    transformStructToClauseSet(struct).map( so => sequentToLabelledSequent( so ) )


  @tailrec
  def transformCartesianProductToStruct(cp: List[Pair[Struct,Struct]],
                                        aux:List[FormulaOccurrence],
                                        acc : List[Struct => Struct]): Struct = cp match {
    case (i,j)::Nil =>
      acc.reverse.foldLeft[Struct](Times(i, j, aux))((struct,fun) => fun(struct))
    case (i,j)::rest =>
      val rec : Struct => Struct = { x => Plus(Times(i,j, aux), x) }
      transformCartesianProductToStruct(rest,aux, rec::acc)

    case Nil =>
      acc.reverse.foldLeft[Struct](EmptyPlusJunction())((struct,fun) => fun(struct))
  }

  private def merge(s1:Struct, s2:Struct, aux: List[FormulaOccurrence]):Struct = {
    val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))
    val cartesianProduct = for (i <- list1; j <- list2) yield (i,j)
    transformCartesianProductToStruct(cartesianProduct, aux, Nil)
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
object SimplifyStruct {
  def apply(s:Struct) : Struct = s match {
    case EmptyPlusJunction() => s
    case EmptyTimesJunction() => s
    case A(_) => s
    case Dual(EmptyPlusJunction()) => EmptyTimesJunction()
    case Dual(EmptyTimesJunction()) => EmptyPlusJunction()
    case Dual(x) => Dual(SimplifyStruct(x))
    case Times(x,EmptyTimesJunction(),_) => SimplifyStruct(x)
    case Times(EmptyTimesJunction(),x,_) => SimplifyStruct(x)
    case Times(x,Dual(y), aux) if x.formula_equal(y) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times(Dual(x),y, aux) if x.formula_equal(y) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times(x,y,aux) =>
      //TODO: adjust aux formulas, they are not needed for the css construction, so we can drop them,
      // but this method should be as general as possible
      Times(SimplifyStruct(x), SimplifyStruct(y), aux)
    case PlusN(terms)  =>
      //println("Checking pluses of "+terms)
      assert(terms.nonEmpty, "Implementation Error: PlusN always unapplies to at least one struct!")
      val nonrendundant_terms = terms.foldLeft[List[Struct]](Nil)((x,term) => {
        val simple = SimplifyStruct(term)
        if (x.filter(_.formula_equal(simple)).nonEmpty )
          x
        else
          simple::x
      })
      /*
      val saved = nonrendundant_terms.size - terms.size
      if (saved >0)
        println("Removed "+ saved + " terms from the struct!")
        */
      PlusN(nonrendundant_terms.reverse)

  }
}


object renameCLsymbols {
  def createMap(cs: List[Sequent]): Map[HOLExpression, HOLExpression] = {
    var i: Int = 1
    var map = Map.empty[HOLExpression, HOLExpression]
    cs.foreach(seq => {
      (seq.antecedent ++ seq.succedent).foreach(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if (constant.name.isInstanceOf[ClauseSetSymbol]) => {
            if (!map.contains(constant)) {
              map = map + Pair(constant, HOLConst("cl_"+i.toString, Tindex->To) )
              i = i + 1
            }
          }
          case _ => {}
        }
      })
    })
    return map
  }
  
  def apply(cs: List[Sequent]): (List[FSequent], Map[HOLExpression, HOLExpression]) = {
    val map = createMap(cs)
    val list = cs.map(seq => {
      val ant = seq.antecedent.map(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if (constant.name.isInstanceOf[ClauseSetSymbol]) => {
            if (map.contains(constant)) {
              HOLApp(map(constant), indices.head)
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
              HOLApp(map(constant), indices.head)
            }
            else
              throw new Exception("\nError in renameCLsymbols.apply !\n")
          }
          case _ => fo.formula
        }
      })
      FSequent(ant.asInstanceOf[List[HOLFormula]], succ.asInstanceOf[List[HOLFormula]])
    })
    (list,map)
  }
}
