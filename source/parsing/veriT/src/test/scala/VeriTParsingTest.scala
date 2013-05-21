package at.logic.parsing.veriT

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit

@RunWith(classOf[JUnitRunner])
class VeriTParsingTest extends SpecificationWithJUnit {

  "The veriT parser" should {
    "parse correctly the simplest proof of the database" in {
      val formulas = VeriTParser.read("target/test-classes/simple.verit")
      //println("\nNumber of axioms: " + formulas.size)
      //println("The formulas that occur in the axioms of this proof are:")
      //formulas.foreach(f => println(f))
      formulas must haveSize(2)
    }

    "parse correctly a more complicated example" in {
      val formulas = VeriTParser.read("target/test-classes/less_simple.verit")
      //println("\nNumber of axioms: " + formulas.size)
      //println("The formulas that occur in the axioms of this proof are:")
      //formulas.foreach(f => println(f))
      formulas must haveSize(74)
    }
  }
}

