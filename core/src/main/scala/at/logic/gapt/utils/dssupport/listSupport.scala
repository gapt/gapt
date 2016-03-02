/**
 * Auxiliar functions operating on lists
 *
 */

package at.logic.gapt.utils.dssupport

object ListSupport {

  /** all lists obtainable by concatenating one from s1 with one from s2 */
  def times[T]( s1: List[List[T]], s2: List[List[T]] ): List[List[T]] = {
    s1.flatMap( c1 => s2.map( c2 => c1 ++ c2 ) )
  }

  /**
   * For each 3rd component which occurs in the list, remove all but the last element
   * with that 3rd component.
   */
  def distinct3rd[T, R]( l: List[Tuple3[String, T, R]] ): List[Tuple3[String, T, R]] = {
    l match {
      case head :: tail =>
        if ( tail.map( tri => tri._3 ).contains( head._3 ) )
          distinct3rd( tail )
        else
          head :: distinct3rd( tail )
      case Nil => Nil
    }
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

