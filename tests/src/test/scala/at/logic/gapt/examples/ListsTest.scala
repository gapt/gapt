package at.logic.gapt.examples

import at.logic.gapt.examples.induction.lists
import org.specs2.mutable.Specification

class ListsTest extends Specification {
  "lists" in {
    import lists._
    for ( proof <- Seq( appnil, appassoc, apprev, revrev, mapapp, maprev, mapfusion ) )
      ctx.check( proof )
    ok
  }
}
