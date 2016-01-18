package at.logic.gapt.utils

object SortedMap {
  def unapplySeq[T, S]( map: Map[T, S] ): Option[Seq[( T, S )]] =
    Some( map.toSeq.sortBy { _.toString } )
}
