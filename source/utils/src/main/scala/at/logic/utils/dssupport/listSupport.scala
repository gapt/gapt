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
  
  def lst2string[T](fun: T => String, separator: String, l:List[T]) : String = l match {
    case Nil => ""
    case List(x) => fun(x)
    case x::xs => fun(x)  + separator + lst2string(fun, separator, xs)
  }

  /** Identical to foldLeft, but with addition function which returns when the folding should be aborted.
    * If that function returns False for an element, the folding is aborted and the result of the last execution
    * of the folding function is returned.
    *
    * @param acc The initial value and the first argument of the folding function.
    * @param list The list of elements to fold.
    * @param cont The function specifying when to abort.
    * It is executed for each list element before the folding function.
    * @param f The folding function which takes the accumulated value and the next list element
    * and returns a the next accumulated value.
    */
  def foldLeftWhile[A,B](acc:B, list:Iterable[A], cont: A => Boolean, f:(B,A) => B) : B = {
    if (list.isEmpty || !cont(list.head)) { acc }
    else { foldLeftWhile(f(acc,list.head), list.tail, cont, f) }
  }

  /** A safe version of List.head which never fails.
    * 
    * @param xs The list of which to return the head.
    * @param default The value to return in case the list is empty.
    * @return xs.head if xs is not empty, otherwise default.
    */
  def safeHead[A](xs:List[A], default:A) : A = xs match {
    case Nil => default
    case (x::_) => x
  }

  def remove_doubles[T](l:List[T]) : List[T] = remove_doubles_(l.reverse).reverse
  private def remove_doubles_[T](l:List[T]) : List[T] = l match {
    case Nil => Nil
    case x::xs => if (xs contains x) remove_doubles_(xs) else x::remove_doubles_(xs)
  }
}

