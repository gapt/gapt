/*
 * abstractTypedLambdaCalculus.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language


object Types {
    abstract class TA {
        def ->(that:TA) = new ->(this, that)
    }
    abstract class TAtomicA extends TA
    abstract class TComplexA extends TA
    case class Ti() extends TAtomicA ; def i = Ti()
    case class To() extends TAtomicA ; def o = To()
    case class ->(in:TA, out:TA) extends TComplexA

}