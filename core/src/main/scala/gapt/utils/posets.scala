package gapt.utils

import scala.collection.mutable

object linearizeStrictPartialOrder {

  /**
   * Linearizes a strict partial order.
   *
   * @param set The set of elements on which the relation is defined.
   * @param relation The relation to be linearized.
   * @tparam T The type of the elements.
   * @return Either (right) a sequence of elements e1,...,en containing all the
   * input elements such that ei `relation` ej implies i < j, for 1 <= i,j <= n,
   * if the input relation is a strict partial order. Otherwise, a cycle (left)
   * is returned.
   */
  def apply[T](
    set:      Iterable[T],
    relation: Iterable[( T, T )] ): Either[Vector[T], Vector[T]] =
    apply(
      set,
      Map().withDefaultValue( Nil ) ++
        relation.groupBy( _._1 ).view.mapValues( Nil ++ _.map( _._2 ) ).toMap )

  def apply[T](
    set:      Iterable[T],
    relation: T => Iterable[T] ): Either[Vector[T], Vector[T]] = {
    val out = mutable.Buffer[T]()
    val seen = mutable.Set[T]()

    case class CycleException( cycle: Vector[T] ) extends Throwable

    def go( t: T, stacktrace: List[T], stacktraceSet: Set[T] ): Unit = {
      if ( seen( t ) ) {
        return
      }
      if ( stacktraceSet( t ) ) {
        throw CycleException(
          Vector( t ) ++ stacktrace.takeWhile( _ != t ).reverseIterator :+ t )
      }
      val stacktrace_ = t :: stacktrace
      val stacktraceSet_ = stacktraceSet + t
      relation( t ).foreach { go( _, stacktrace_, stacktraceSet_ ) }
      out.prepend( t )
      seen += t
    }

    try {
      for ( s <- set ) go( s, List(), Set() )
      Right( out.toVector )
    } catch {
      case CycleException( cycle ) => Left( cycle )
    }
  }
}

object generatedUpperSetInPO {
  def apply[T]( gen: Iterable[T], rel: Iterable[( T, T )] ): Set[T] = {
    val upper = mutable.Set[T]()
    def walk( el: T ): Unit =
      if ( !upper.contains( el ) ) {
        upper += el
        for ( case ( `el`, next ) <- rel ) walk( next )
      }
    gen foreach walk
    upper.toSet
  }
}

object transitiveClosure {
  def apply[T]( rel: Iterable[( T, T )] ): Set[( T, T )] = {
    val adjList = Map() ++ ( for ( ( a, g ) <- rel.groupBy( _._1 ) ) yield a -> g.map( _._2 ).toSet )
    val upperSets = mutable.Map[T, Set[T]]()
    def upperSet( a: T ): Set[T] =
      upperSets.getOrElseUpdate( a, adjList.getOrElse( a, Set.empty ).flatMap( upperSet ) )
    for ( a <- rel.map( _._1 ).toSet ++ rel.map( _._2 ); b <- upperSet( a ) ) yield a -> b
  }
}
