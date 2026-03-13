package gapt.utils

/**
* Computes the cartesian product of the given sequence of iterables.
* If the input is a sequence of sets A_1,...,A_n this returns
* returns an iterator of all tuples (a_1, ..., a_n)
* such that a_i is in A_i.
* If the inner iterables contain duplicate elements, then the output will also contain
* duplicate tuples
*
* @param xss list of sets to compute cartesian product of
* @return an iterator of all tuples of the cartesian product
*/
def cartesianProduct[A](xss: Seq[Iterable[A]]): Iterator[Seq[A]] = {
  xss.foldLeft(Iterator(Seq.empty[A])) { (acc, xs) =>
    for {
      a <- acc
      x <- xs
    } yield a :+ x
  }
}
