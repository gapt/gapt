/*
 * Multisets.scala
 *
 * None mathematical definition of mutlisets. I.e. multisets code does not follow the scala convention of defining mathematical objects in mathematical terms (multiset as a function (A => Int)),
 * as we want the multiset to be covariant. We will only follow the interface that two multisets are equal if they have the same amount of the same elements.
 */

package at.logic.utils.ds

import scala.collection.immutable.{HashMap, HashSet}

object Multisets {

//    trait Multiset[+A] extends Iterable[A]{
    trait Multiset[A] extends Iterable[A] {
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

      def iterator = map.keys.iterator

      override def equals( that: Any ) = that match {
        case x : HashMultiset[A] => {
          map.equals( x.map )
        }
        case _ => false
      }

      override def hashCode = map.hashCode

      override def toString = map.toString
    }

  object HashMultiset {
    def apply[A]() = new HashMultiset(new HashMap[A,Int])
  }

  // some combinatorics: return the set of all multisets
  // that can be obtained by drawing at most n elements
  // from a given multiset

  def combinations[A]( n: Int, m: Multiset[A] ) : Set[Multiset[A]] = n match {
    case 0 => HashSet() + HashMultiset()
    case _ => m.foldLeft( HashSet[Multiset[A]]() )( (res, elem) => {
      val s = combinations( n - 1, m - elem )
      res ++ s ++ s.map( m => m + elem )
    } )
  }
}

