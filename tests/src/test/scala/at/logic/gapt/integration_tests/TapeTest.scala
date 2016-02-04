package at.logic.gapt.integration_tests

import at.logic.gapt.expr.{ Eq, FOLAtom }
import at.logic.gapt.proofs.SequentMatchers
import at.logic.gapt.proofs.lk._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.formats.llk.LatexLLKExporter
import at.logic.gapt.proofs.ceres.{ deleteTautologies, _ }
import java.io.File.separator

import at.logic.gapt.examples.tape
import org.specs2.mutable._

class TapeTest extends Specification with SequentMatchers {
  "The system" should {

    "parse, skolemize, extract and refute the css of the tape proof" in {
      val proof_sk = skolemize( regularize( DefinitionElimination( tape.defs )( tape.p ) ) )
      //println( LatexLLKExporter( proof_sk, true ) )

      println( proof_sk )
      val s = StructCreators.extract( proof_sk )

      println( s"struct: $s" )
      val cs_ = CharacteristicClauseSet( s )
      println( cs_.size )
      val cs = deleteTautologies( cs_ )
      cs.map( x => println( s"Clause: $x" ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs.toList )
      println( s"tptp string:\n$tptp" )
      //      val writer = new java.io.FileWriter( "target" + separator + "tape-cs.tptp" )
      //      writer.write( tptp.toString )
      //      writer.flush
      val projs = Projections( proof_sk )
      //projs.toList.map( x => { println( x.endSequent diff proof_sk.endSequent ) } )
      println( LatexLLKExporter( projs.toList( 0 ), true ) )
      cs.map( x => {
        print( s"projection for clause $x " )
        projs.exists( _.endSequent.diff( proof_sk.endSequent ) setEquals x ) match {
          case true =>
            println( " found!" );
          case false =>
            println( " not found!" )
        }
        //cs.asInstanceOf[Set[HOLSequent]].contains( pes ) must beTrue
      } )

      Escargot getResolutionProof cs must beSome
    }

    "apply the full CERES method" in {
      //get the proof
      val proof = skolemize( regularize( DefinitionElimination( tape.defs )( tape.p ) ) )
      val ancf = CERES( proof, Escargot )
      ancf.endSequent must beMultiSetEqual( proof.endSequent )

    }

    "apply the full CERES method and skip cuts on equations" in {
      val proof = skolemize( regularize( DefinitionElimination( tape.defs )( tape.p ) ) )
      val acnf = CERES( proof, CERES.skipEquations, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }

    "apply the full CERES method and skip cuts on equations, then cut-eliminate cuts of equations" in {
      //get the proof
      val proof = skolemize( regularize( DefinitionElimination( tape.defs )( tape.p ) ) )
      val acnf = CERES( proof, CERES.skipEquations, Escargot )
      val eqacnf = CERES( acnf, _ match { case Eq( _, _ ) => true; case FOLAtom( _, _ ) => false; case _ => true }, Escargot )
      eqacnf.endSequent must beMultiSetEqual( proof.endSequent )

    }

  }
}
