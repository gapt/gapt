/*
 * streams.scala
 *
 * Some utility functions for Scala streams.
 */

package at.logic.utils.ds
import scala.collection.immutable.Stream.Empty

package streams {
  object Definitions {

    def even[A]( s: Stream[A] ) : Stream[A] = if (s.isEmpty) Empty else
      Stream.cons( s.head, even(s.tail.tail) )

    def odd[A]( s: Stream[A] ) : Stream[A] = if (s.isEmpty) Empty
      else if (s.tail.isEmpty) Empty
      else Stream.cons( s.tail.head, odd(s.tail.tail) )

  }
}
