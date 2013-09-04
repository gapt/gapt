package at.logic.parsing.veriT

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit

@RunWith(classOf[JUnitRunner])
class VeriTParsingTest extends SpecificationWithJUnit {

  "The veriT parser" should {
    "parse correctly the simplest proof of the database" in {
      //println("------------------- TEST 0 ------------------------")
      val formulas = VeriTParser.read("target/test-classes/test0.verit")
      //println("\nNumber of formulas on the antecedent: " + formulas._1.size)
      //println("Formulas on the antecedent:")
      //formulas._1.foreach(f => println(f))
      formulas._1 must haveSize(2)
    }

    "parse correctly a more complicated example" in {
      //println("------------------- TEST 1 ------------------------")
      val formulas = VeriTParser.read("target/test-classes/test1.verit")
      //println("\nNumber of formulas on the antecedent: " + formulas._1.size)
      //println("Formulas on the antecedent:")
      //formulas._1.foreach(f => println(f))
      // Only 3 expansion trees: input, eq_transitive (with a million
      // instances!) and eq_symmetry (with hundreds of instances)
      formulas._1 must haveSize(3)
    }
    
    "parse correctly an even more complicated example" in {
      //println("------------------- TEST 2 ------------------------")
      val formulas = VeriTParser.read("target/test-classes/test2.verit")
      //println("\nNumber of formulas on the antecedent: " + formulas._1.size)
      //println("Formulas on the antecedent:")
      //formulas._1.foreach(f => println(f))
      formulas._1 must haveSize(4)
    }
  }
}

