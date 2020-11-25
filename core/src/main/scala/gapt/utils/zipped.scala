package gapt.utils

object zipped {

  /**
   * Zips two sequences of elements.
   *
   * @param is1 The left components
   * @param is2 The right components
   * @tparam T1 The left component type
   * @tparam T2 The right component type
   * @return A sequence of pairs obtained by zipping `is1` with `is2`.
   */
  def apply[T1, T2]( is1: Iterable[T1], is2: Iterable[T2] ): Iterable[( T1, T2 )] =
    is1.lazyZip( is2 )

  /**
   * @see `zipped.apply[T1,T2](T1,T2)`.
   */
  def apply[T1, T2]( is: ( Iterable[T1], Iterable[T2] ) ): Iterable[( T1, T2 )] =
    zipped( is._1, is._2 )
}
