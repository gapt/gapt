/**
 * Auxiliar functions operating on lists
 *
 */

package at.logic.utils.dssupport

//import scala.actors._

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

  def removeFirst[A](s: Seq[A], a: A): Seq[A] = {
    val index = s.indexOf(a)
    s.take(index) ++ s.takeRight(s.size-index-1)
  }

  def removeFirst[A](s: List[A], a: A): List[A] = removeFirstWhere(s, (x:A) => a == x)

  def removeFirstWhere[A](s: List[A], prop : A => Boolean): List[A] = s match {
    case Nil => Nil
    case x::xs if prop(x) => xs
    case x::xs /* !prop(x) */ => x::removeFirstWhere(xs,prop)
  }
  
  /** Given a list xs, returns a list of copies of xs without the first, second, ..., last element.
    *
    *
    */
  def listComplements[T](xs: Seq[T]) : Seq[Seq[T]] = xs match {
    case Nil     => Nil
    case y +: ys => ys +: listComplements(ys).map(zs => y +: zs)
  }
  /** Given a list xs, returns a list of copies of xs without the nth, ..., last element.
    *
    *
    */  
  def listComplements[T](xs: Seq[T], n: Int) : Seq[Seq[T]] = {
    val (fst, snd) = xs splitAt (n-1)
    listComplements(snd).map(zs => fst ++ zs)
  }
  
  def listComplements_[T](xs: Seq[T]) : Seq[(T,Seq[T])] = xs match {
    case Nil     => Nil
    case y +: ys => (y,ys) +: listComplements_(ys).map(p => (p._1, y +: p._2))
  }
  
  /** Splits a list into (nth element, elements 1,..,(n-1), elements (n+1),..,end)
    * @param xs The list to split.
    * @param n  The position to split at.
    */
  def zipper[T](xs: Seq[T], n: Int) : (T, Seq[T], Seq[T]) = xs match {
    case Nil     => throw new IllegalArgumentException
    case y +: ys => {
      if (n == 1)
        (y, Nil, ys)
      else {
        val (z, fst, snd) = zipper(ys, n-1)
        (z, y +: fst, snd)
      }
    }
  }
  
  /** Groups sequence xs into subsequences of elements that have the same image under function f.
    * @param xs The sequence to be partitioned.
    * @param f  The function.
    */
  def groupSeq[A, B](xs: Seq[A], f: A => B): Seq[Seq[A]] = xs match {
    case Nil => Nil
    case y +: ys => {
      val z = f(y)
      val zs = y +: ys.filter(x => (f(x) == z))
      val rest = ys.filterNot(x => (f(x) == z))
      zs +: groupSeq(rest, f)
    }
  }
  
  def pairwiseImages[A,B,C](xs: Seq[A], ys: Seq[B], f: (A,B) => C): Seq[Seq[C]] = xs match {
    case Nil => Nil
    case z +: zs => ys.map(y => f(z,y)) +: pairwiseImages(zs, ys, f)
  }

  /**
   * Generates the powerset S as a List of a List, where
   * |S| <= n
   *
   * @param s list
   * @param n upperbound for the powerset
   * @tparam A type of the list
   * @return bounded powerset
   */
  def boundedPower[A](s: List[A], n: Int): List[List[A]] = {
    // init powerset
    val powerset = List[List[A]]()

    // function for generating a subset of the powerset of a particular size
    def genLists(l: List[A], i:Int, n: Int): List[List[A]] = l match {
      // if no elements are left terminate
      case Nil        => List[List[A]]()
      // if we can still add an element
      // EITHER do not add it and leave i (size of already chosen elements) as it is
      // OR add it and increment i
      case a :: as  if i+1 < n  => genLists(as,i,n) ++ (genLists(as,i+1,n) map (a :: _))
      // if we can add just one more element
      // either do so, or not
      case a :: as  if i+1 >= n => List(List(a)) ++ genLists(as,i,n)
    }
    // call genLists for 1 <= i <= n times
    // and concatenate all results, s.t. we get the intended result
    (for (i <- List.range(1, n+1)) yield genLists(s,0,i)).foldLeft(List[List[A]]())( (prevLists,l) => prevLists ++ l)
  }

  /**
   * Generates out of a list l
   * the diagonal cartesian product l² of it
   * minus the diagonal and mirrorcases
   *
   * @param l list of elements
   * @return diagonal cartesian product of l
   */
  def diagCross(l:List[Int]) : List[(Int,Int)] = {
    l match {
      case x::xs => xs.map(y => (x,y)) ++ diagCross(xs)
      case _ => Nil
    }
  }

}

