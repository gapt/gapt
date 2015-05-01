package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.language.fol.algorithms.convertHolToFol
import at.logic.gapt.language.hol._
import at.logic.gapt.proofs.lk.algorithms.{ AtomicExpansion, deleteTautologies, map_proof, regularize }
import at.logic.gapt.proofs.resolution.algorithms.RobinsonToLK
import at.logic.gapt.proofs.resolution.{ Clause, ResolutionProof }
import at.logic.gapt.proofs.lk._

import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._

import at.logic.gapt.provers.atp.Prover
import at.logic.gapt.provers.atp.commands.base.SetStreamCommand
import at.logic.gapt.provers.atp.commands.sequents.SetTargetClause
import at.logic.gapt.provers.prover9._

import at.logic.gapt.proofs.algorithms.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.algorithms.ceres.clauseSets.profile.proofProfile
import at.logic.gapt.proofs.algorithms.ceres.projections.Projections
import at.logic.gapt.proofs.algorithms.ceres.struct.StructCreators
import at.logic.gapt.proofs.algorithms.ceres.{ CERES, CERESR2LK }

import at.logic.gapt.proofs.algorithms.skolemization.lksk.LKtoLKskc
import at.logic.gapt.proofs.algorithms.skolemization.skolemize

import commands.Prover9InitCommand
import at.logic.gapt.algorithms.rewriting.DefinitionElimination

import java.io.File.separator
import java.io.{ IOException, FileInputStream, InputStreamReader }
import java.util.zip.GZIPInputStream

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class TapeTest extends SpecificationWithJUnit {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  sequential
  "The system" should {
    "parse correctly the tape proof" in {
      val proofdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      /*
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = setNormalize( dcs )

      saveXML( Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::Nil, "target" + separator + "tape-cs.xml" )
      */
      ok
    }

    "parse, skolemize and extract the profile of the tape proof" in {
      checkForProverOrSkip

      val proofdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      val prf = deleteTautologies( proofProfile( s, proof_sk ).map( _.toFSequent ) )

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter( "target" + separator + "tape-prf.tptp" )
      writer_prf.write( tptp_prf )
      writer_prf.flush

      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter( "target" + separator + "tape-cs.tptp" )
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "tape-sk.xml"

      val prf_cs_intersect = prf.filter( seq => cs.contains( seq ) )

      Prover9.refute( prf ) match {
        case None      => "" must beEqualTo( "refutation of proof profile failed" )
        case Some( _ ) => true must beEqualTo( true )
      }
      Prover9.refute( cs ) match {
        case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
        case Some( _ ) => true must beEqualTo( true )
      }

      saveXML( Tuple2( "tape-sk", proof_sk ) ::
        projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2( "cs", cs ) :: Tuple2( "prf", prf ) :: Tuple2( "cs_prf_intersection", prf_cs_intersect ) :: Nil, path )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
    }

    "apply prover9 to the tape proof clause set" in {
      checkForProverOrSkip

      val proofdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )

      object MyProver extends Prover[Clause]

      def getRefutation( ls: Iterable[FSequent] ): Boolean = MyProver.refute( Stream( SetTargetClause( FSequent( List(), List() ) ), Prover9InitCommand( ls ), SetStreamCommand() ) ).next must beLike {
        case Some( a ) if a.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals ( FSequent( List(), List() ) ) => ok
        case _ => ko
      }

      getRefutation( cs.map( _.toFSequent ) ) must beTrue
    }

    "create an acnf of the tape proof via ground proof" in {
      checkForProverOrSkip
      //get the proof
      val pdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "the-proof" ) ) ) )
      val ( foltape, _ ) = map_proof( elp, convertHolToFol.apply )

      //get the refutation of the clause set, refute it
      val tapecl = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( foltape ) )
      val Some( taperp ) = Prover9.refute( tapecl.map( _.toFSequent ) )
      val lkref = RobinsonToLK( taperp )

      //get projections etc
      val tapeproj = Projections( foltape )
      val refproj = CERES.refProjection( foltape.root.toFSequent )

      val acnf = CERES( foltape.root.toFSequent, tapeproj + refproj, lkref )

      //the acnf must not contain any quantified cuts
      acnf.nodes.collect( { case c @ CutRule( _, _, _, aux, _ ) if containsQuantifier( aux.formula ) => c } ) must beEmpty
      acnf.root.toFSequent must beSyntacticFSequentEqual( foltape.root.toFSequent )

    }

    "create an acnf of the tape proof via robinson2lk" in {
      checkForProverOrSkip
      //get the proof
      val pdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "the-proof" ) ) ) )
      val ( foltape, _ ) = map_proof( elp, convertHolToFol.apply )

      //get the refutation of the clause set, refute it
      val tapecl = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( foltape ) )
      val Some( taperp ) = Prover9.refute( tapecl.map( _.toFSequent ) )

      //get projections etc
      val tapeproj = Projections( foltape )
      val refproj = CERES.refProjection( foltape.root.toFSequent )

      val acnf = CERESR2LK( foltape.root.toFSequent, tapeproj + refproj, taperp )

      //the acnf must not contain any quantified cuts
      acnf.nodes.collect( { case c @ CutRule( _, _, _, aux, _ ) if containsQuantifier( aux.formula ) => c } ) must beEmpty
      acnf.root.toFSequent must beSyntacticFSequentEqual( foltape.root.toFSequent )

    }

  }
}
