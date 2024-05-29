/*
 * streams.scala
 *
 * Some utility functions for Scala streams.
 */

package gapt.utils

object StreamUtils {

  def even[A](s: LazyList[A]): LazyList[A] = if (s.isEmpty) LazyList.empty
  else
    LazyList.cons(s.head, even(s.tail.tail))

  def odd[A](s: LazyList[A]): LazyList[A] = if (s.isEmpty) LazyList.empty
  else if (s.tail.isEmpty) LazyList.empty
  else LazyList.cons(s.tail.head, odd(s.tail.tail))

}
