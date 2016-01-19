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
   * Generates the powerset S as a List of a List, where
   * |S| <= n
   *
   * @param s list
   * @param n upperbound for the powerset
   * @tparam A type of the list
   * @return bounded powerset
   */
  def boundedPower[A]( s: List[A], n: Int ): List[List[A]] = {
    // init powerset
    val powerset = List[List[A]]()

    // function for generating a subset of the powerset of a particular size
    def genLists( l: List[A], i: Int, n: Int ): List[List[A]] = l match {
      // if no elements are left terminate
      case Nil                   => List[List[A]]()
      // if we can still add an element
      // EITHER do not add it and leave i (size of already chosen elements) as it is
      // OR add it and increment i
      case a :: as if i + 1 < n  => genLists( as, i, n ) ++ ( genLists( as, i + 1, n ) map ( a :: _ ) )
      // if we can add just one more element
      // either do so, or not
      case a :: as if i + 1 >= n => List( List( a ) ) ++ genLists( as, i, n )
    }
    // call genLists for 1 <= i <= n times
    // and concatenate all results, s.t. we get the intended result
    ( for ( i <- List.range( 1, n + 1 ) ) yield genLists( s, 0, i ) ).foldLeft( List[List[A]]() )( ( prevLists, l ) => prevLists ++ l )
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

