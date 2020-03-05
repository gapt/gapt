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

  def crossProduct[T]( lists: Iterable[Iterable[T]] ): Iterable[List[T]] = lists match {
    case Nil          => List( Nil )
    case head :: rest => for { x <- head; y <- crossProduct( rest ) } yield x :: y
  }

}
