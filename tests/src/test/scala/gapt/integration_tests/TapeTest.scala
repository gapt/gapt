package gapt.integration_tests

import gapt.examples.tape
import gapt.expr.formula.Eq
import gapt.expr.formula.fol.FOLAtom
import gapt.formats.tptp.TptpFOLExporter
import gapt.proofs.SequentMatchers
import gapt.proofs.ceres._
import gapt.proofs.ceres.deleteTautologies
import gapt.proofs.context.Context
import gapt.proofs.lk._
import gapt.proofs.lk.transformations.skolemizeLK
import gapt.provers.escargot.Escargot
import gapt.provers.prover9.Prover9
import org.specs2.mutable._

class TapeTest extends Specification with SequentMatchers {
  "The system" should {

    "parse, skolemizeInferences, extract and refute the css of the tape proof" in {
      val proof_sk = skolemizeLK(tape.proof)
      // println( LatexLLKExporter( proof_sk, true ) )

      //      println( proof_sk )
      val s = StructCreators.extract(proof_sk)(Context())

      //      println( s"struct: $s" )
      val cs_ = CharacteristicClauseSet(s)
      //      println( cs_.size )
      val cs = deleteTautologies(cs_)
      //      cs.map( x => println( s"Clause: $x" ) )
      val tptp = TptpFOLExporter.tptpProblem(cs.toList)
      //      println( s"tptp string:\n$tptp" )
      //      val writer = new java.io.FileWriter( "target" + separator + "tape-cs.tptp" )
      //      writer.write( tptp.toString )
      //      writer.flush
      val projs = Projections(proof_sk)
      // projs.toList.map( x => { println( x.endSequent diff proof_sk.endSequent ) } )
      //      println( LatexLLKExporter( projs.toList( 0 ), true ) )
      cs.map(x => {
        //        print( s"projection for clause $x " )
        projs.exists(_.endSequent.diff(proof_sk.endSequent) setEquals x) match {
          case true =>
          //            println( " found!" );
          case false =>
          //            println( " not found!" )
        }
        // cs.asInstanceOf[Set[HOLSequent]].contains( pes ) must beTrue
      })

      Escargot getResolutionProof cs must beSome
    }

    "apply the full CERES method" in {
      // get the proof
      val proof = skolemizeLK(tape.proof)
      val ancf = CERES(proof, Escargot)
      tape.ctx.check(ancf)
      ancf.endSequent must beMultiSetEqual(proof.endSequent)
    }

    "apply the full CERES method and skip cuts on equations" in {
      val proof = skolemizeLK(tape.proof)
      val acnf = CERES(proof, CERES.skipEquations, Escargot)
      tape.ctx.check(acnf)
      acnf.endSequent must beMultiSetEqual(proof.endSequent)
    }

    "apply the full CERES method and skip cuts on equations, then cut-eliminate cuts of equations" in {
      skipped("resulting LK proof has a few million inferences")
      // get the proof
      val proof = skolemizeLK(tape.proof)
      val acnf = CERES(proof, CERES.skipEquations, Escargot)
      val eqacnf = CERES(acnf, _ match { case Eq(_, _) => true; case FOLAtom(_, _) => false; case _ => true }, Prover9)
      tape.ctx.check(eqacnf)
      eqacnf.endSequent must beMultiSetEqual(proof.endSequent)

    }

  }
}
