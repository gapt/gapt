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

}
