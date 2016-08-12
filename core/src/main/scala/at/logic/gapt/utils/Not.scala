package at.logic.gapt.utils

/**
 * Together with the scala `<:<` construct, the Not trait allows us to express that a type is not a subtype of another. This works in the following manner:
 * Suppose you have types `S <: T` and a function `foo[T]` that you only want to apply to elements of type T that are not of type S.
 * Then you can write `foo[T](implicit notAnS: Not[S <:<T])`.
 *
 * TODO: Add an "ambiguous implicit" annotation to make this clearer. My scala version does not currently support this.
 *
 * @tparam T
 */
sealed trait Not[T]

object Not {
  implicit def default[T]: Not[T] = null
  implicit def specific[T]( implicit ev: T ): Not[T] = null
}
