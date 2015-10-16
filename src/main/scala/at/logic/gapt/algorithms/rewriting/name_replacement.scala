package at.logic.gapt.algorithms.rewriting

object NameReplacement {

  /* creates a mapping from elements in objects to targets. the predicate matches indicates when two elements should
     be considered to match each */
  def find_matching[A, B]( objects: List[A], targets: List[B], matches: ( A, B ) => Boolean ): Map[A, B] = {
    objects match {
      case x :: xs =>
        val ( prefix, suffix ) = targets.span( !matches( x, _ ) )
        suffix match {
          case el :: rest => find_matching( xs, prefix ++ rest, matches ) + ( ( x, el ) )
          case Nil        => throw new Exception( "Can not find a match for element " + x + " in " + targets )
        }

      case Nil =>
        if ( targets.isEmpty )
          Map[A, B]()
        else
          throw new Exception( "Want to create a matching of sets of different size! remaining elements: " + targets )
    }
  }

}
