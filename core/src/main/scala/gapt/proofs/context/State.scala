package gapt.proofs.context

import gapt.proofs.context.facet.Facet

import scala.reflect.ClassTag

/**
 * The state of a context.
 *
 * A context remembers both its history (what elements were added to it),
 * as well as their effect: the current state (the values of the facets).
 *
 * State is basically a Cartesian product of all possible facets, where all except
 * finitely many facets still have their initial value.  The [[get]] method returns
 * the value of a facet, the [[update]] method changes the value.
 */
class State private ( private val facets: Map[Facet[_], Any] ) {
  def update[T: Facet]( f: T => T ): State =
    new State( facets.updated( implicitly[Facet[T]], f( get[T] ) ) )

  def get[T: Facet]: T =
    facets.getOrElse( implicitly[Facet[T]], implicitly[Facet[T]].initial ).asInstanceOf[T]

  def getAll[T: ClassTag]: Iterable[T] =
    facets.values.collect { case t: T => t }

  override def toString: String = {
    val s = new StringBuilder
    for ( ( f, d ) <- facets.toSeq.sortBy( _._1.toString ) ) {
      s ++= s"$f:"
      val dStr = d.toString
      if ( dStr.contains( "\n" ) ) {
        s.append( "\n  " ).append( dStr.replace( "\n", "\n  " ) )
      } else {
        s.append( " " ).append( dStr )
      }
      s ++= "\n\n"
    }
    s.result()
  }
}
object State {
  def apply(): State = new State( Map() )
}