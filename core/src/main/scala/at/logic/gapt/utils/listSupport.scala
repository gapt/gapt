/**
 * Auxiliar functions operating on lists
 *
 */

package at.logic.gapt.utils

object ListSupport {

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

