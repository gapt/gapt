package gapt.examples

import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments

class MonoidCancellationTest extends Specification {

  Fragments.foreach( 0 to 100 by 10 ) { i =>
    s"$i" in {
      MonoidCancellation.runBenchmark( i )
      ok
    }
  }

}
