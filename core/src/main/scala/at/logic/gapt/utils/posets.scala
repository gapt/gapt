package at.logic.gapt.utils

import scala.collection.mutable

object linearizeStrictPartialOrder {
  def apply[T]( set: Iterable[T], relation: Iterable[( T, T )] ): Either[Seq[T], Seq[T]] =
    build( set.toSet, relation.toSet, Seq() )

  private def build[T]( set: Set[T], relation: Set[( T, T )], prefix: Seq[T] ): Either[Seq[T], Seq[T]] =
    if ( set isEmpty ) {
      Right( prefix )
    } else {
      set find { n => relation forall { _._2 != n } } match {
        case Some( next ) =>
          build( set - next, relation filterNot { _._1 == next }, prefix :+ next )
        case None =>
          Left( findCycle( set.head, relation ) )
      }
    }

  private def findCycle[T]( start: T, relation: Set[( T, T )] ): Seq[T] = {
    def walkDown( start: T, alreadyVisited: List[T] ): Seq[T] = {
      val Some( ( _, next ) ) = relation find { _._2 == start }
      if ( alreadyVisited contains next )
        next :: ( alreadyVisited.takeWhile( _ != next ) :+ next )
      else
        walkDown( next, next :: alreadyVisited )
    }
    walkDown( start, start :: Nil )
  }

  private def walkDown[T]( start: T, relation: Set[( T, T )] ): Stream[T] = {
    val Some( ( _, next ) ) = relation find { _._2 == start }
    start #:: walkDown( next, relation )
  }
}

object generatedUpperSetInPO {
  def apply[T]( gen: Iterable[T], rel: Iterable[( T, T )] ): Set[T] = {
    val upper = mutable.Set[T]()
    def walk( el: T ): Unit =
      if ( !upper.contains( el ) ) {
        upper += el
        for ( ( `el`, next ) <- rel ) walk( next )
      }
    gen foreach walk
    upper.toSet
  }
}
