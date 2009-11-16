/*
 * ExpressionIdentities.scala
 *
 * This file supply traits and convenience classes to wrap LambdaExpressions with some ID so they can be easily retrieved from sequents.
 */

package at.logic.calculi

import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.lambda.Types._
import at.logic.language.hol.HigherOrderLogic._
import at.logic.utils.labeling.Labels._

object ExpressionOccurrences {

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


    
    // parameterized by the element used as an id (which must be orderable via an implicit conversion)
    abstract class Occurrence extends Labeled[Occur] {
        def merge(other: Occurrence): Occur = CombinedOccur(label, other.label)
    }

    case class FormulaOccurrence[+A <: HOL](formula: Formula[A], val label: Occur) extends Occurrence
}
