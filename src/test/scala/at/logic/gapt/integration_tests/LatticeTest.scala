/**
 * Description:
 */
package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.algorithms.{ getStatistics, deleteTautologies }
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.provers.prover9._
import at.logic.gapt.proofs.algorithms.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.algorithms.ceres.clauseSets.profile._
import at.logic.gapt.proofs.algorithms.ceres.projections.Projections
import at.logic.gapt.proofs.algorithms.ceres.struct.StructCreators
import at.logic.gapt.proofs.algorithms.skolemization.lksk.LKtoLKskc
import at.logic.gapt.proofs.algorithms.skolemization.skolemize

import java.io.File.separator
import java.io.{ IOException, FileReader, FileInputStream, InputStreamReader }
import java.util.zip.GZIPInputStream
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class LatticeTest extends SpecificationWithJUnit {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  def sequentToString( s: Sequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toString + ", " )
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toString + ", " )
    ret
  }

  def printStats( p: LKProof ) = {
    val stats = getStatistics( p )
    print( "unary: " + stats.unary + "\n" )
    print( "binary: " + stats.binary + "\n" )
    print( "cuts: " + stats.cuts + "\n" )
  }

  sequential
  "The system" should {
    "parse, transform to LKsk, and extract the clause set for the lattice proof" in {
      val proofdb = ( new XMLReader( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "lattice.xml" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      //printStats( proof )

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      /*
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = setNormalize( dcs )
      val cs_path = "target" + separator + "lattice-cs.xml"
      saveXML( Nil, Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::Nil, cs_path )
      (new java.io.File( cs_path ) ).exists() must beEqualTo( true )
*/
      ok
    }

    "parse and skolemize the lattice proof" in {
      checkForProverOrSkip

      val proofdb = ( new XMLReader( new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "lattice.xml" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      val prf = deleteTautologies( proofProfile( s, proof_sk ).map( _.toFSequent ) )

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter( "target" + separator + "lattice-prf.tptp" )
      writer_prf.write( tptp_prf )
      writer_prf.flush

      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter( "target" + separator + "lattice-cs.tptp" )
      writer.write( tptp )
      writer.flush

      val prf_cs_intersect = prf.filter( seq => cs.contains( seq ) )

      // refute it with prover9
      Prover9.refute( prf ) match {
        case None      => "" must beEqualTo( "refutation of proof profile failed" )
        case Some( _ ) => true must beEqualTo( true )
      }
      Prover9.refute( cs ) match {
        case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
        case Some( _ ) => true must beEqualTo( true )
      }

      val projs = Projections( proof_sk )
      val path = "target" + separator + "lattice-sk.xml"
      saveXML( Tuple2( "lattice-sk", proof_sk ) ::
        projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        // projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2( "cs", cs ) :: Tuple2( "prf", prf ) :: Tuple2( "cs_prf_intersection", prf_cs_intersect ) :: Nil, path )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
    }
  }
}
