package at.logic.gapt.formats.veriT

import java.io.InputStreamReader

import org.specs2.mutable._

class VeriTParsingTest extends Specification {

  def parseClasspathFile( filename: String ) =
    VeriTParser.getExpansionProof( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( filename ) ) )

  "The veriT parser" should {
    "parse correctly the simplest proof of the database" in {
      val formulas = parseClasspathFile( "test0.verit" )
      formulas.get.antecedent must haveSize( 2 )
    }

    "parse correctly a more complicated example" in {
      val formulas = parseClasspathFile( "test1.verit" )
      // Only 3 expansion trees: input, eq_transitive (with a million
      // instances!) and eq_symmetry (with hundreds of instances)
      formulas.get.antecedent must haveSize( 2 )
    }

    "parse correctly an even more complicated example" in {
      val formulas = parseClasspathFile( "test2.verit" )
      formulas.get.antecedent must haveSize( 3 )
    }

    "parse correctly an example from QG-classification" in {
      val formulas = parseClasspathFile( "test3.verit" )
      formulas.get.antecedent must haveSize( 8 )
    }
    "parse correctly a different eq_congruent 1" in {
      val formulas = parseClasspathFile( "iso_icl439.smt2.proof_flat" )
      formulas.get.antecedent must haveSize( 14 )
    }
    // If the test above is commented out. This one fails with stackoverflow o.O
    "parse correctly a different eq_congruent 2" in {
      val formulas = parseClasspathFile( "test4.verit" )
      formulas.get.antecedent must haveSize( 10 )
    }
  }
}

