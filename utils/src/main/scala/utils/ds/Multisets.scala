/*
 * Multisets.scala
 *
 * None mathematical definition of mutlisets. I.e. multisets code does not follow the scala convention of defining mathematical objects in mathematical terms (multiset as a function (A => Int)),
 * as we want the multiset to be covariant. We will only follow the interface that two multisets are equal if they have the same amount of the same elements.
 */

package at.logic.utils.ds

import scala.collection.immutable.HashMap

object Multisets {

//    trait Multiset[+A] extends Iterable[A]{
    trait Multiset[A] {
      def + (elem: A) : Multiset[A]
      def - (elem: A) : Multiset[A]
    }

    class HashMultiset[A](val map: HashMap[A, Int]) extends Multiset[A] {
      def + (elem: A) = new HashMultiset( map + (( elem, map.getOrElse(elem, 0) + 1 ) ))

      def - (elem: A)  = new HashMultiset( if (map.contains(elem))
        if (map.get(elem).get == 1)
          map - (elem)
        else
          map + ((elem, map.get(elem).get - 1))
      else
        throw new Exception // element not contained in the multiset
      )
    }

  object HashMultiset {
    def apply[A]() = new HashMultiset(new HashMap[A,Int])
  }
}

