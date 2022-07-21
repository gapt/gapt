package gapt

package object utils {

  def unorderedPairsOf[T]( elements: Iterable[T] ): Iterable[( T, T )] = {
    val elementsWithIndex = elements.zipWithIndex
    for {
      ( e1, i1 ) <- elementsWithIndex
      ( e2, i2 ) <- elementsWithIndex
      if i1 < i2
    } yield ( e1, e2 )
  }

  def crossProduct[T]( xs: Seq[Iterable[T]] ): Iterable[Seq[T]] =
    xs match {
      case Seq()              => Seq( Seq() )
      case Seq( x, xss @ _* ) => for { y <- x; ys <- crossProduct( xss ) } yield y +: ys
    }

  def symmetricClosure[T]( xs: Set[( T, T )] ): Set[( T, T )] =
    xs ++ xs.map { case ( x1, x2 ) => x2 -> x1 }

  object shortestPath {

    import scala.collection.mutable

    object comparator extends Ordering[Option[Int]] {
      override def compare( x: Option[Int], y: Option[Int] ): Int =
        ( x, y ) match {
          case ( None, None )           => 0
          case ( None, Some( _ ) )      => 1
          case ( Some( _ ), None )      => -1
          case ( Some( x ), Some( y ) ) => Ordering.Int.compare( x, y )
        }
    }

    def apply[N]( start: N, target: N, edges: Set[( N, N )], weight: ( N, N ) => Int ): Option[Seq[N]] = {

      val predecessor: mutable.Map[N, N] = mutable.Map()
      val cost: mutable.Map[N, Int] = mutable.Map()
      val next: mutable.Set[N] = mutable.Set()
      val workedOff: mutable.Set[N] = mutable.Set()

      cost( start ) = 0
      next += start

      while ( next.nonEmpty ) {
        val n = next.minBy( { n => cost.get( n ) } )( comparator )
        next.remove( n )
        workedOff += n
        val ns = neighbors( n ).filter { !workedOff.contains( _ ) }
        next ++= ns
        for ( v <- ns ) {
          if ( cost.get( v ).map { _ > cost( n ) + weight( n, v ) }.getOrElse( true ) ) {
            cost( v ) = cost( n ) + weight( n, v )
            predecessor( v ) = n
          }
        }
      }

      def neighbors( n: N ): Set[N] = edges.filter { _._1 == n }.map { _._2 }

      def path( n: N ): Seq[N] = {
        def path_( n: N ): Seq[N] = {
          Seq( n ) ++ ( predecessor.get( n ) match {
            case None      => Seq()
            case Some( p ) => path_( p )
          } )
        }
        path_( n ).reverse
      }

      predecessor.get( target ) match {
        case None      => None
        case Some( _ ) => Some( path( target ) )
      }
    }
  }

}
