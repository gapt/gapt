/*
 * Multisets.scala
 *
 * None mathematical definition of mutlisets. I.e. multisets code does not follow the scala convention of defining mathematical objects in mathematical terms (multiset as a function (A => Int)),
 * as we want the multiset to be covariant. We will only follow the interface that two multisets are equal if they have the same amount of the same elements.
 */

package at.logic.utils.ds

object Multisets {

    trait Multiset[+A] extends Iterable[A]{
    }

    /*class HashMultiset[+A] extends Multiset[A] {
        
    }*/
}

