/*
 * Tests for the prover9 interface.
**/

package at.logic.gapt.provers.prover9

import at.logic.gapt.formats.simple.SimpleFOLParser
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.occurrences.factory
import at.logic.gapt.proofs.resolution.robinson.{ Formatter, RobinsonResolutionProof }
import at.logic.gapt.language.fol._
import at.logic.gapt.formats.readers.StringReader
import java.io.File.separator
import java.io.IOException

import at.logic.gapt.utils.testing.ClasspathFileCopier
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class Prover9Test extends SpecificationWithJUnit with ClasspathFileCopier {
  def parse( str: String ): FOLFormula = ( new StringReader( str ) with SimpleFOLParser getTerm ).asInstanceOf[FOLFormula]

  implicit def fo2occ( f: FOLFormula ) = factory.createFormulaOccurrence( f, Nil )

  args( skipAll = !Prover9.isInstalled )
  "The Prover9 interface" should {
    "not refute { :- P; Q :- }" in {

      val s1 = FSequent( Nil, List( parse( "P" ) ) )
      val t1 = FSequent( List( parse( "Q" ) ), Nil )
      val result: Option[RobinsonResolutionProof] = Prover9.refute( List( s1, t1 ) )
      result match {
        case Some( proof ) =>
          "" must beEqualTo( "Refutation found although clause set satisfiable!" )

        case None => true must beEqualTo( true )
      }
    }

    "prove { :- (All x) x = x   }" in {

      val p = new Prover9Prover()

      val s = FSequent( Nil, List( FOLAllVar( FOLVar( "x" ), parse( "=(x,x)" ) ) ) )

      p.isValid( s ) must beTrue
      // TODO: cannot yet import proofs for arbitrary formulas
      /*  p.getRobinsonProof (s) must beLike {
        case Some(_) => ok
        case None => ko
      } */
    }

    "prove { A or B :- -(-A and -B)  }" in {

      val p = new Prover9Prover()
      val s = FSequent( List( FOLOr( parse( "A" ), parse( "B" ) ) ), List( FOLNeg( FOLAnd( FOLNeg( parse( "A" ) ), FOLNeg( parse( "B" ) ) ) ) ) )

      p.isValid( s ) must beTrue
      p.getRobinsonProof( s ) must beLike {
        case Some( _ ) => ok
        case None      => ko
      }
    }

    "handle quantified antecedents" in {

      val g1 = parse( "Forall x Forall y =(+(s(x), y), s(+(x, y)))" )
      val g2 = parse( "Forall z =(+(o, z), z)" )
      val g0 = parse( "And =(z, o) =(z, w)" )
      val f = parse( "=(+(+(z, s(s(o))), s(s(o))), +(s(s(o)), +(s(s(o)), w)))" )

      Prover9.prove( FSequent( List( g0, g1, g2 ), List( f ) ) ) must beLike {
        case Some( _ ) => ok
        case None      => ko
      }
    }

  }

  "The Prover9 interface" should {
    "successfully load the goat puzzle PUZ047+1.out" in {
      // if the execution of prooftrans does not work: skip test
      Prover9.parse_prover9( tempCopyOfClasspathFile( "PUZ047+1.out" ) )

      "success" must beEqualTo( "success" )
    }

    "successfully load the expansion proof paper example cade13example.out" in {
      // if the execution of prooftrans does not work: skip test
      Prover9.parse_prover9( tempCopyOfClasspathFile( "cade13example.out" ) )

      "success" must beEqualTo( "success" )
    }

    "successfully load a proof with new_symbol" in {
      val p = Prover9.parse_prover9( tempCopyOfClasspathFile( "ALG138+1.out" ) )
      Formatter.asHumanReadableString( p._1 )
      ok
    }

  }

  "The Prover9 interface" should {
    "load a Prover9 proof and verify the validity of the sequent" in {
      for ( testfilename <- "PUZ047+1.out" :: "ALG138+1.out" :: "cade13example.out" :: Nil ) {
        val ( robResProof, seq, _ ) = Prover9.parse_prover9( tempCopyOfClasspathFile( testfilename ) )
        ( new Prover9Prover ).isValid( seq ) must beTrue
      }
      ok
    }
  }

}
