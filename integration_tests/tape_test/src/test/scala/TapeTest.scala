/**
 * Description:
**/
package at.logic.integration_tests


import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.Clause
import _root_.at.logic.provers.atp.commands.base.SetStreamCommand
import _root_.at.logic.provers.atp.commands.sequents.SetTargetClause
import _root_.at.logic.provers.atp.commands.sequents.SetTargetClause._
import _root_.at.logic.provers.atp.Prover
import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml.saveXML

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk._
import at.logic.transformations.skolemization.lksk.LKtoLKskc

import base.Sequent._
import base.types._
import java.util.zip.GZIPInputStream
import java.io.File.separator

import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.projections.Projections
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.algorithms.fol.hol2fol._
import at.logic.language.fol._
import at.logic.transformations.ceres.clauseSets.profile.proofProfile
import at.logic.provers.prover9._
import commands.Prover9InitCommand
import commands.Prover9InitCommand._
import java.io.{IOException, FileReader, FileInputStream, InputStreamReader}


class TapeTest extends SpecificationWithJUnit {
  val box = List()
  def checkForProverOrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip


  "The system" should {
    "parse correctly the tape proof" in {
      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "tape-in.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqual(1)
      val proof = proofdb.proofs.head._2

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      /*
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = setNormalize( dcs )

      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Nil, "target" + separator + "test-classes" + separator + "tape-cs.xml" )
      */
    }
    "parse, skolemize and extract the profile of the tape proof" in {
      checkForProverOrSkip

      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "tape-in.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqual(1)
      val proof = proofdb.proofs.head._2

      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      val prf = deleteTautologies(proofProfile(s, proof_sk).map( _.toFSequent ))

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter("target" + separator + "test-classes" + separator + "tape-prf.tptp")
      writer_prf.write( tptp_prf )
      writer_prf.flush

      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter("target" + separator + "test-classes" + separator + "tape-cs.tptp")
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "test-classes" + separator + "tape-sk.xml"

      val prf_cs_intersect = prf.filter(seq => cs.contains(seq))

      Prover9.refute( cs ) must beEqual( true )
      Prover9.refute( prf ) must beEqual( true )


      saveXML( Pair("tape-sk", proof_sk) ::
        projs.map( p => p._1 ).toList.zipWithIndex.map( p => Pair( "\\psi_{" + p._2 + "}", p._1 ) ),
        Pair("cs", cs)::Pair("prf",prf)::Pair("cs_prf_intersection", prf_cs_intersect)::Nil, path )
      (new java.io.File( path ) ).exists() must beEqual( true )
    }
    "apply prover9 to the tape proof clause set" in {
      Prover9.refute(List()) must not(throwA[IOException]).orSkip

      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "tape-in.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqual(1)
      val proof = proofdb.proofs.head._2

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )

      object MyProver extends Prover[Clause]

      def getRefutation(ls: Iterable[FSequent]): Boolean = MyProver.refute(Stream(SetTargetClause((List(),List())), Prover9InitCommand(ls), SetStreamCommand())).next must beLike {
        case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals (List(),List()) => true
        case _ => false
      }
      getRefutation(cs.map(_.toFSequent)) must beTrue
    }
  }
}
