/*
 * lists.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */


package at.logic.utils.ds
import at.logic.utils.logging.Logger

/** Contains various utility functions for lists.
  */
package lists {

  object Definitions {
    /** Performs a map with an accumulator.
      * Useful for e.g. mapping a custom counter onto a collection.
      *
      * @param f The mapping function. Takes an accumulator and an element from the list and returns a tuple
      *        of the new accumulator value and the mapped list element.
      * @param init The initial accumulator value.
      * @param list The list on which to perform the map.
      * @return The mapped list and the final value of the accumulator.
      */
    def mapAccumL[Acc,X,Y](f:(Acc, X) => (Acc,Y), init:Acc, list:List[X]):(Acc,List[Y]) = list match {
      case Nil => (init, Nil)
      case (x::xs) => {
        val (new_acc, y) = f(init, x)
        val (new_acc2,ys) = mapAccumL(f, new_acc, xs)

        (new_acc2, y::ys)
      }
    }
  }
}
