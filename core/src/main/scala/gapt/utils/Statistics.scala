package gapt.utils

/**
 * Holds the statistic parameters of a collection of elements of type a numerical type T
 *
 * @param n the size of the data
 * @param min the minimal element
 * @param max the maximal element
 * @param avg the average element
 * @param median the median element
 * @param sigma_square the square of the standard deviation (only exists for n >= 2)
 * @tparam T the type of elements the collection contains
 */

case class Statistic[T](
    n:            Int,
    min:          T,
    max:          T,
    avg:          BigDecimal,
    median:       BigDecimal,
    sigma_square: Option[BigDecimal] ) {

  /**
   * exports the statistics as a list of strings
   */
  lazy val toCSV = List( n.toString, min.toString, max.toString, avg.toString, median.toString,
    sigma_square.map( _.toString ).getOrElse( "NA" ) )
}

object Statistic {
  //create a list of descriptions of the for tag-min that matches the order of Statistic.toCSV
  def csv_header( tag: String ) = List( "min", "max", "avg", "median", "deviation" ).map( x => s"$tag-$x" )

  /**
   * Creates a statistic from a collection of values of type T.
   * @param values the collection of values
   * @param num the implicit Numeric object with implementations for the algebraic operators
   * @param conv a measure that maps the elements of T to big decimals
   * @tparam T the type of elements
   * @return the statistic belonging to the values
   */
  def apply[T]( values: Seq[T] )( implicit num: Numeric[T], conv: T => BigDecimal ): Statistic[T] = {
    require( values.nonEmpty, "Need data to compute statistics" )

    val sorted = values.sorted

    val _n = values.size
    val _min: T = values.min
    val _max: T = values.max
    val _bdvalues = values.map( conv )
    val _sum: BigDecimal = _bdvalues.sum //convert to big numbers before summing up

    val _avg: BigDecimal = _sum / BigDecimal( _n )

    val _sigma_square: Option[BigDecimal] =
      if ( _n >= 2 ) Some( _bdvalues.map( x => ( _avg - x ) pow 2 ).sum / ( _n - 1 ) )
      else None

    val _median: BigDecimal = _n % 2 match {
      case 0 =>
        val m1: BigDecimal = sorted( _n / 2 )
        val m2: BigDecimal = sorted( ( _n / 2 ) - 1 )
        ( m1 + m2 ) / 2
      case 1 =>
        sorted( _n / 2 )
      case _ =>
        throw new IllegalArgumentException( "Result of % 2 should always be 0 or 1!" )
    }

    new Statistic[T]( _n, _min, _max, _avg, _median, _sigma_square )
  }

}
