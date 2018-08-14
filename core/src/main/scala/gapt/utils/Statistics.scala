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

@SerialVersionUID( 700100L )
case class Statistic[T](
    n:            Int,
    min:          T,
    max:          T,
    avg:          BigDecimal,
    median:       BigDecimal,
    sigma_square: Option[BigDecimal] ) extends Serializable {

  /**
   * exports the statistics as a list of strings
   */
  lazy val toCSV = List( n.toString, min.toString, max.toString, avg.toString, median.toString,
    sigma_square.map( _.toString ).getOrElse( Statistic.na ) )
}

/**
 * Companion object to [[Statistic]]. Provides a csv header and convenience methods for statistic options and empty
 * data lists.
 */
object Statistic {
  val na = "NA"

  /**
   * create a list of descriptions of the form tag-min, tag-max etc. that matches the order of Statistic.toCSV
   * @param tag the prefix for the columns
   */
  def csv_header( tag: String ) = List( "count", "min", "max", "avg", "median", "deviation" ).map( x => s"$tag-$x" )

  /**
   * static "not applicable" CSV value for a non-existing statistic
   */
  val na_statistic = Statistic( 0 :: Nil ).toCSV map ( _ => na )

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

  /**
   * Converts a statistic option to CSV with a default of not applicable
   * @param s an optional statistic
   * @tparam T the type of data elements of the statistic
   * @return CSV data for s, if it exists [[na_statistic]] otherwise
   */
  def optCSV[T]( s: Option[Statistic[T]] ) = s match {
    case None                    => na_statistic
    case Some( s: Statistic[T] ) => s.toCSV
  }

  /**
   * Produces CSV data of statistics for non-empty data, and 'not applicable' values otherwise.
   * @param s a sequence of data
   * @param num the implicit converter to treat elements of s as numeric types
   * @param conv a measure for calculating the avarage and standard deviation in the statistic
   * @tparam T the type of data to create statistics on  (must be measurable in terms of num and conv)
   * @return CSV data for s if it is non-empty, [[Statistic.na_statistic]] otherwise
   */
  def alsoEmptyDataToCSV[T]( s: Seq[T] )( implicit num: Numeric[T], conv: T => BigDecimal ): Seq[String] =
    if ( s.isEmpty ) na_statistic else Statistic( s ).toCSV

  def print[T]( s: Statistic[T] ) = {
    println( s"n  : ${s.n}" )
    println( s"min: ${s.min}" )
    println( s"max: ${s.max}" )
    println( s"med: ${s.median}" )
    println( s"avg: ${s.avg}" )
    s.sigma_square.map( x => println( s"sd2: $x" ) )
  }

}
