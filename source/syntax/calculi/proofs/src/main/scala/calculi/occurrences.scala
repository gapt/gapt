/*
 * ExpressionIdentities.scala
 *
 * This file supply traits and convenience classes to wrap LambdaExpressions with some ID so they can be easily retrieved from sequents.
 */

package at.logic.calculi

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.utils.labeling._
import scala.collection.immutable.Set

/**
 * The user can use abstract occurrences that mark different formulas or use positions as occurrences
 */
package occurrences {

  class OccurrenceException(msg: String) extends Exception(msg)

  trait Occurrence extends Labeled {
  }

  trait FOFactory {
    def createPrincipalFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence]): FormulaOccurrence
    def createContextFormulaOccurrence(formula: HOLFormula, current: FormulaOccurrence, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence]): FormulaOccurrence =
       createContextFormulaOccurrence(formula, current, ancestors, others, Set.empty[FormulaOccurrence]) // the offset is used to tell there is a binary rule and the number of formulas in the
    def createContextFormulaOccurrence(formula: HOLFormula, current: FormulaOccurrence, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence], binary_others: Set[FormulaOccurrence]): FormulaOccurrence
  }

  // formula occurrences have also a specific id to compare without regard to the occurrence
  object FOID {
    var id: BigInt = 0 // this enumerates all formula occurrences used in the system. Please make sure their number does not exceed the max_int value
  }
  // equality is done by reference so each two generated formula occurrences are different
  abstract class FormulaOccurrence(val formula: HOLFormula, val ancestors: List[FormulaOccurrence]) extends Occurrence {
    def factory: FOFactory
    val id = {FOID.id = FOID.id + 1; FOID.id}
    def =^(a: FormulaOccurrence) = a.id == id // normal equality compares occurrences and not specific formula occurrences object, use this method to refer to specific instances
  }
   /*
  // abstract occurrences
  // Occurs are equal if they are syntactically equal or one contains the other
  abstract class Occur {
    def size: Int
  }
  case class BaseOccur(vl: Int) extends Occur {
    def size = 1
    override def equals(a: Any) = a match {
      case b: BaseOccur => vl == b.vl
      case b: CombinedOccur => b.equals(this)
      case _ => false
    }
  }
  case class CombinedOccur(vl1: Occur, vl2: Occur) extends Occur {
    def size = vl1.size + vl2.size
    override def equals(a: Any) = a match {
      case b: BaseOccur => vl1.equals(b) || vl2.equals(b)
      case b: CombinedOccur =>
        if (size == b.size) (vl1.equals(b.vl1) && vl2.equals(b.vl2))
        else if (size > b.size) (vl1.equals(b) || vl2.equals(b))
        else (b.vl1.equals(this) || b.vl2.equals(this))
      case _ => false
    }
  }
  class AbstractOccurrence(occ: Occur) extends Occurrence[Occur] {
    def merge(other: AbstractOccurrence): Occur = CombinedOccur(label, other.label)
    def label = occ 
  }
              */

  object PositionsFOFactory extends FOFactory {
    // always add at the max+1 position
    def createPrincipalFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence]): FormulaOccurrence = {
      val othersCast = others.asInstanceOf[Set[IntOccurrence]]
      val max = othersCast.foldLeft(0)((prev, fo) => scala.math.max(prev, fo.label))
      new FormulaOccurrence(formula, ancestors) with IntOccurrence {def factory = PositionsFOFactory; def label = max+1}
    }
    // we check how many are before the position and then substract them if needed. binary_others is used to add as prefix the size of the set of the left upper rule
    def createContextFormulaOccurrence(formula: HOLFormula, current: FormulaOccurrence, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence], binary_others: Set[FormulaOccurrence]): FormulaOccurrence = {
      val othersCast = others.asInstanceOf[Set[IntOccurrence]]
      val currentCast = current.asInstanceOf[IntOccurrence]
      val pos = othersCast.filter(x => x< currentCast).size + 1
      new FormulaOccurrence(formula, ancestors) with IntOccurrence {def factory = PositionsFOFactory; def label = pos + binary_others.size}
    }

  }

  trait IntOccurrence extends Occurrence with Ordered[IntOccurrence] {
    type T = Int // sets the type of Labeled
    override def equals(a: Any) = a match {
      case s: IntOccurrence => label == s.label
      case s: Int => label == s
      case _ => false
    }
    def compare (that: IntOccurrence) = label compare that.label
  }
  
  // user wanting to use positions should import the following object
  object positions {
    implicit val positionFactory = PositionsFOFactory
    implicit def fromIntToPosition(s:Int):IntOccurrence = new IntOccurrence{def label = s}
  }

  // another possible occurrences type is by object address, i.e. any two occurrences are different and you must use an existing one in order to refer to a specific occurrence
  // (unike positions where you can also use any instance of a position)

  trait PointerOccurrence extends Occurrence {
    type T = Occurrence // sets the type of Labeled
    def label = this
    override def equals(a: Any) = a match {
      case s: PointerOccurrence => label == s.label 
      case _ => false
    }
  }
}
