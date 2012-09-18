/**
 * Auxiliar functions operating on lists
 *
 */

package at.logic.utils.dssupport

object ListSupport {

  // Cartesian product of an arbitrary list of lists
  def product[T](l: List[List[T]]): List[List[T]] = l match {
    case Nil => List(Nil)
      case h :: t => for(eh <- h; et <- product(t)) yield eh :: et
  }

  // Find all subsets
  def subsets[T](s : List[T]) : List[List[T]] = {
    if (s.size == 0) List(List()) 
    else { 
      val tailSubsets = subsets(s.tail); 
      tailSubsets ++ tailSubsets.map(s.head :: _) 
    }
  }

}

