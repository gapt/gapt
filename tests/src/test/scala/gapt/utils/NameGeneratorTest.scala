package gapt.utils

import org.specs2.mutable.Specification

class NameGeneratorTest extends Specification {

  "generated names based on pattern" in {
    "should conform to pattern" in {
      val pattern = (n: Int) => s"name_${n}"
      (new NameGenerator(Nil)).freshWithIndex(pattern) mustEqual pattern(0)
    }

    "should be fresh" in {
      val pattern = (n: Int) => s"name_${n}"
      val generator = new NameGenerator(List("name_0"))
      generator.freshWithIndex(pattern) mustEqual pattern(1)
    }

    "should be minimal" in {
      val pattern = (n: Int) => s"name_${n}"
      (new NameGenerator(Nil)).freshWithIndex(pattern) mustEqual pattern(0)
    }
  }
}
