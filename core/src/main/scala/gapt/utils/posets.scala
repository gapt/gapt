package gapt.utils

import scala.collection.mutable

object linearizeStrictPartialOrder {
  def apply[T]( set: Iterable[T], relation: Iterable[( T, T )] ): Either[Vector[T], Vector[T]] =
    apply( set, Map().withDefaultValue( Nil ) ++ relation.groupBy( _._1 ).mapValues( Nil ++ _.map( _._2 ) ) )

  def apply[T]( set: Iterable[T], relation: T => Iterable[T] ): Either[Vector[T], Vector[T]] = {
    val out = mutable.Buffer[T]()
    val printed = mutable.Set[T]()

    case class CycleException( cycle: Vector[T] ) extends Throwable

    def go( t: T, stacktrace: List[T], stacktraceSet: Set[T] ): Unit =
      if ( printed( t ) ) {
      } else if ( stacktraceSet( t ) ) {
        throw CycleException( Vector( t ) ++ stacktrace.takeWhile( _ != t ).reverseIterator :+ t )
      } else {
        val stacktrace_ = t :: stacktrace
        val stacktraceSet_ = stacktraceSet + t
        relation( t ).foreach( go( _, stacktrace_, stacktraceSet_ ) )
        out.prepend( t )
        printed += t
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
        for ( ( `el`, next ) <- rel ) walk( next )
      }
    gen foreach walk
    upper.toSet
  }
}
