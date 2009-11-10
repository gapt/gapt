/*
 * ExpressionIdentities.scala
 *
 * This file supply traits and convenience classes to wrap LambdaExpressions with some ID so they can be easily retrieved from sequents.
 */

package at.logic.calculi.lk

import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.hol.HigherOrderLogic._
import at.logic.utils.labeling.Labels._

object ExpressionOccurrences {

    abstract class Occur[A]
    case class BaseOccur[A](vl: A) extends Occur[A]
    case class CombinedOccur[A](vl1: Occur[A], vl2: Occur[A]) extends Occur[A]
    
    // parameterized by the element used as an idea (which must be orderable via an implicit conversion)
    trait Occurrence[A] extends Labeled[Occur[A]] {
        def merge(other: Occurrence[A]): Occur[A] = CombinedOccur(label, other.label)
    }

    case class FormulaOccurrence[+A <: HOL](formula: Formula[A], val label: Occur[Int]) extends Occurrence[Int]
}
