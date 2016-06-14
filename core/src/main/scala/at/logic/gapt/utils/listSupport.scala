/**
 * Auxiliar functions operating on lists
 *
 */

package at.logic.gapt.utils

object ListSupport {

  /** all lists obtainable by concatenating one from s1 with one from s2 */
  def times[T]( s1: List[List[T]], s2: List[List[T]] ): List[List[T]] = {
    s1.flatMap( c1 => s2.map( c2 => c1 ++ c2 ) )
  }

  def removeFirstWhere[A]( s: List[A], prop: A => Boolean ): List[A] = s match {
    case Nil                    => Nil
    case x :: xs if prop( x )   => xs
    case x :: xs /* !prop(x) */ => x :: removeFirstWhere( xs, prop )
  }

  /**
   *
   * @param xs A list.
   * @tparam A The type of list elements.
   * @return A list containing all ordered pairs of elements of xs, excluding the diagonal.
   */
  def pairs[A]( xs: Seq[A] ): Seq[( A, A )] = xs match {
    case Seq() => Seq()
    case y +: ys =>
      ( ys map { ( _, y ) } ) ++ ( ys map { ( y, _ ) } ) ++ pairs( ys )
  }

}

