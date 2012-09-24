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

  // Computes the transpose of a matrix implemented as a list of lists.
  def transpose[T](m: List[List[T]]) : List[List[T]] = m match {
    case Nil => Nil
    case (Nil) :: tl => Nil
    case hd :: tl => 
      val heads = m.foldRight(List[T]()) ( (lst, acc) => lst.head :: acc )
      val tails = m.foldRight(List[List[T]]()) ( (lst, acc) => lst.tail :: acc )
      heads::transpose(tails)             
  }

}

