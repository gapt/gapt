/*
 * streams.scala
 *
 * Some utility functions for Scala streams.
 */

package gapt.utils

import scala.collection.immutable.Stream.Empty

object StreamUtils {

  def even[A]( s: Stream[A] ): Stream[A] = if ( s.isEmpty ) Empty else
    Stream.cons( s.head, even( s.tail.tail ) )

  def odd[A]( s: Stream[A] ): Stream[A] = if ( s.isEmpty ) Empty
  else if ( s.tail.isEmpty ) Empty
  else Stream.cons( s.tail.head, odd( s.tail.tail ) )

}
