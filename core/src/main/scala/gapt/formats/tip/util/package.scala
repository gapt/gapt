package gapt.formats.tip

package object util {

  object find {
    def apply[T](
      elements: Seq[T], p: ( T ) => Boolean ): Option[( Seq[T], T, Seq[T] )] = {
      val index = elements.indexWhere( p )
      if ( index == -1 ) {
        None
      } else {
        Some( (
          elements.take( index ),
          elements( index ),
          elements.drop( index + 1 ) ) )
      }
    }
  }

}
