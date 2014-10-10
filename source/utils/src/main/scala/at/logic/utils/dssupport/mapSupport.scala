/**
 * Auxiliar functions operating on maps
 *
 */

package at.logic.utils.dssupport

object MapSupport {

  // Given a map of T1 elements associated with a list of T2 elements, returns
  // all possible maps that associate each T1 element with at most one of its
  // T2 elements.
  // E.g.:
  // Map:
  // 1 -> a, b
  // 2 -> c
  // Map product:
  // 1 -> a  |   1 -> b
  // 2 -> c  |   2 -> c
  def mapProduct[T1, T2](m: Map[T1, List[List[T2]]]): List[Map[T1, List[T2]]] = {
    val forms = m.keySet.toList
    forms match {
      case Nil => List(Map.empty)
      case h :: t => for(eh <- m(h); et <- mapProduct(m - (h))) yield et + (h -> eh)
    }
  }
  
  def addNoOverwrite[A,B](m: Map[A,B], k: A, v: B): Map[A,B] = {
    if (!m.contains(k))
      m + ((k,v))
    else
      m
  }

}


