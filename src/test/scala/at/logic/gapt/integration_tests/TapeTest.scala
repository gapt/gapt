package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.resolution.RobinsonToLK
import at.logic.gapt.proofs.resolution.{ OccClause, ResolutionProof }

import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._

import at.logic.gapt.provers.atp.Prover
import at.logic.gapt.provers.atp.commands.base.SetStreamCommand
import at.logic.gapt.provers.atp.commands.sequents.SetTargetClause
import at.logic.gapt.provers.prover9._

import at.logic.gapt.proofs.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.ceres.clauseSets.profile.proofProfile
import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators
import at.logic.gapt.proofs.ceres.{ CERES, CERESR2LK }

import commands.Prover9InitCommand
import at.logic.gapt.algorithms.rewriting.DefinitionElimination

import java.io.File.separator
import java.io.{ IOException, FileInputStream, InputStreamReader }
import java.util.zip.GZIPInputStream

import org.specs2.mutable._

class TapeTest extends Specification {
  def checkForProverOrSkip = new Prover9Prover().isInstalled must beTrue.orSkip

  sequential
  "The system" should {
    "parse correctly the tape proof" in {
      val proofdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk = LKToLKsk( proof )
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

      val prf = deleteTautologies( proofProfile( s, proof_sk ).map( _.toHOLSequent ) )

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter( "target" + separator + "tape-prf.tptp" )
      writer_prf.write( tptp_prf )
      writer_prf.flush

      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toHOLSequent ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter( "target" + separator + "tape-cs.tptp" )
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "tape-sk.xml"

      val prf_cs_intersect = prf.filter( seq => cs.contains( seq ) )

      new Prover9Prover().getRobinsonProof( prf ) match {
        case None      => "" must beEqualTo( "refutation of proof profile failed" )
        case Some( _ ) => true must beEqualTo( true )
      }
      new Prover9Prover().getRobinsonProof( cs ) match {
        case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
        case Some( _ ) => true must beEqualTo( true )
      }

      saveXML(
        Tuple2( "tape-sk", proof_sk ) ::
          projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2( "cs", cs ) :: Tuple2( "prf", prf ) :: Tuple2( "cs_prf_intersection", prf_cs_intersect ) :: Nil, path
      )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
    }

    "apply prover9 to the tape proof clause set" in {
      checkForProverOrSkip

      val proofdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk = LKToLKsk( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )

      object MyProver extends Prover[OccClause]

      def getRefutation( ls: Iterable[HOLSequent] ): Boolean = MyProver.refute( Stream( SetTargetClause( HOLSequent( List(), List() ) ), Prover9InitCommand( ls ), SetStreamCommand() ) ).next must beLike {
        case Some( a ) if a.asInstanceOf[ResolutionProof[OccClause]].root syntacticMultisetEquals ( HOLSequent( List(), List() ) ) => ok
        case _ => ko
      }

      getRefutation( cs.map( _.toHOLSequent ) ) must beTrue
    }

    "create an acnf of the tape proof via ground proof" in {
      checkForProverOrSkip
      //get the proof
      val pdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "the-proof" ) ) ) )

      //get the refutation of the clause set, refute it
      val tapecl = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( elp ) )
      val Some( taperp ) = new Prover9Prover().getRobinsonProof( tapecl.map( _.toHOLSequent ) )
      val lkref = RobinsonToLK( taperp )

      //get projections etc
      val tapeproj = Projections( elp )
      val refproj = CERES.refProjection( elp.root.toHOLSequent )

      val acnf = CERES( elp.root.toHOLSequent, tapeproj + refproj, lkref )

      //the acnf must not contain any quantified cuts
      acnf.nodes.collect( { case c @ CutRule( _, _, _, aux, _ ) if containsQuantifier( aux.formula ) => c } ) must beEmpty
      acnf.root.toHOLSequent must beSyntacticFSequentEqual( elp.root.toHOLSequent )

    }

    "create an acnf of the tape proof via robinson2lk" in {
      checkForProverOrSkip

      //get the proof
      val pdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "the-proof" ) ) ) )

      //get the refutation of the clause set, refute it
      val tapecl = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( elp ) )
      val Some( taperp ) = new Prover9Prover().getRobinsonProof( tapecl.map( _.toHOLSequent ) )

      //get projections etc
      val tapeproj = Projections( elp )
      val refproj = CERES.refProjection( elp.root.toHOLSequent )

      val acnf = CERESR2LK( elp.root.toHOLSequent, tapeproj + refproj, taperp )

      //the acnf must not contain any quantified cuts
      acnf.nodes.collect( { case c @ CutRule( _, _, _, aux, _ ) if containsQuantifier( aux.formula ) => c } ) must beEmpty
      acnf.root.toHOLSequent must beSyntacticFSequentEqual( elp.root.toHOLSequent )

    }

  }
}
