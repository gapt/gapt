package gapt.utils

import org.specs2.mutable.Specification

class UtilTests extends Specification{

  "symmetric closure should add missing pair" in {
    symmetricClosure( Set(0 -> 1) ) must_== Set( 0 -> 1, 1 -> 0)
  }

}
