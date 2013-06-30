/**
 * Auxiliar functions operating on lists
 *
 */

package at.logic.utils.dssupport

object ListSupport {

  /** Cartesian product of an arbitrary list of lists */
  def product[T](l: List[List[T]]): List[List[T]] = l match {
    case Nil => List(Nil)
      case h :: t => for(eh <- h; et <- product(t)) yield eh :: et
  }

  /** Find all subsets */
  def subsets[T](s : List[T]) : List[List[T]] = {
    if (s.size == 0) List(List()) 
    else { 
      val tailSubsets = subsets(s.tail); 
      tailSubsets ++ tailSubsets.map(s.head :: _) 
    }
  }

  /** Computes the transpose of a matrix implemented as a list of lists. */
  def transpose[T](m: List[List[T]]) : List[List[T]] = m match {
    case Nil => Nil
    case (Nil) :: tl => Nil
    case hd :: tl => 
      val heads = m.foldRight(List[T]()) ( (lst, acc) => lst.head :: acc )
      val tails = m.foldRight(List[List[T]]()) ( (lst, acc) => lst.tail :: acc )
      heads::transpose(tails)             
  }

  /** A tail-recursive union without duplicate elimination.
    * When order does not matter, ++ can be replaced by this.
    */
  def tailRecUnion[A](xs:List[A],ys:List[A]):List[A] = ys match {
    case Nil => xs
    case (y::yrest) => tailRecUnion(y::xs,yrest)
  }

  /** Performs a map with an accumulator.
    * Useful for e.g. mapping a custom counter onto a collection.
    *
    * @param f The mapping function. Takes an accumulator and an element from the list and returns a tuple
    *        of the new accumulator value and the mapped list element.
    * @param init The initial accumulator value.
    * @param list The list on which to perform the map.
    * @return The mapped list and the final value of the accumulator.
    */
  def mapAccumL[Acc,X,Y](f:(Acc, X) => (Acc,Y), init:Acc, list:List[X]):(Acc,List[Y]) = list match {
    case Nil => (init, Nil)
    case (x::xs) => {
      val (new_acc, y) = f(init, x)
      val (new_acc2,ys) = mapAccumL(f, new_acc, xs)

      (new_acc2, y::ys)
    }
  }
}

