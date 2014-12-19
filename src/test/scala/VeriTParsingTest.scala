package at.logic.parsing.veriT

import at.logic.utils.testing.ClasspathFileCopier
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit

@RunWith(classOf[JUnitRunner])
class VeriTParsingTest extends SpecificationWithJUnit with ClasspathFileCopier {

  "The veriT parser" should {
    "parse correctly the simplest proof of the database" in {
      val formulas = VeriTParser.getExpansionProof(tempCopyOfClasspathFile("test0.verit"))
      formulas.get.antecedent must haveSize(2)
    }

    "parse correctly a more complicated example" in {
      val formulas = VeriTParser.getExpansionProof(tempCopyOfClasspathFile("test1.verit"))
      // Only 3 expansion trees: input, eq_transitive (with a million
      // instances!) and eq_symmetry (with hundreds of instances)
      formulas.get.antecedent must haveSize(3)
    }

    "parse correctly an even more complicated example" in {
      val formulas = VeriTParser.getExpansionProof(tempCopyOfClasspathFile("test2.verit"))
      formulas.get.antecedent must haveSize(4)
    }
    
    "parse correctly an example from QG-classification" in {
      val formulas = VeriTParser.getExpansionProof(tempCopyOfClasspathFile("test3.verit"))
      formulas.get.antecedent must haveSize(9)
    }
    "parse correctly a different eq_congruent 1" in {
      val formulas = VeriTParser.getExpansionProof(tempCopyOfClasspathFile("iso_icl439.smt2.proof_flat"))
      formulas.get.antecedent must haveSize(15)
    }
    // If the test above is commented out. This one fails with stackoverflow o.O
    "parse correctly a different eq_congruent 2" in {
      val formulas = VeriTParser.getExpansionProof(tempCopyOfClasspathFile("test4.verit"))
      formulas.get.antecedent must haveSize(11)
    }
  }
}

