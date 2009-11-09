/*
 * Sets.scala
 *
 * None mathematical definition of sets. I.e. sets code does not follow the scala convention of defining mathematical objects in mathematical terms (set as a function (A => Noolean)),
 * as we want the set to be covariant. We will only follow the interface that two sets are equal if they have the same elements.
 */

package at.logic.utils.ds

object Sets {
    trait Set[+A] extends Collection[A]{
    }

    /*class HashSet[+A] extends Set[A] {

    }*/
}
