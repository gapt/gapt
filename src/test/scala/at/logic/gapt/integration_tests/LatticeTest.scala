/**
 * Description:
 */
package at.logic.gapt.integration_tests

import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.formats.xml.XMLParser._
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.proofs.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.ceres.clauseSets.profile._
import at.logic.gapt.proofs.ceres.extractStructFromLKsk
import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk.{ deleteTautologies, LKToLKsk, getStatistics }
import at.logic.gapt.proofs.lkNew.{ DefinitionElimination, skolemize, lkOld2New, lkNew2Old }
import at.logic.gapt.provers.prover9._
import java.io.File.separator
import java.io.{ IOException, FileReader, FileInputStream, InputStreamReader }
import java.util.zip.GZIPInputStream
import org.specs2.mutable._

class LatticeTest extends Specification {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  def sequentToString( s: OccSequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toString + ", " )
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toString + ", " )
    ret
  }

  def printStats( p: LKProof ) = {
    val nLine = sys.props( "line.separator" )
    val stats = getStatistics( p )
    print( "unary: " + stats.unary + nLine )
    print( "binary: " + stats.binary + nLine )
    print( "cuts: " + stats.cuts + nLine )
  }

  "The system" should {
    "parse, transform to LKsk, and extract the clause set for the lattice proof" in {
      checkForProverOrSkip

      val proofdb = XMLProofDatabaseParser( getClass.getClassLoader.getResourceAsStream( "lattice.xml" ) )
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = DefinitionElimination( proofdb.Definitions )( lkOld2New( proofdb.proofs.head._2 ) )

      val proof_sk = at.logic.gapt.proofs.lkNew.LKToLKsk( proof )
      val s = extractStructFromLKsk( proof_sk )
      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toHOLSequent.asInstanceOf[HOLClause] ) )
      Prover9.getRobinsonProof( cs ) must beSome
    }

    "parse and skolemize the lattice proof" in {
      checkForProverOrSkip

      val proofdb = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "lattice.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      val proof_sk_new = skolemize( lkOld2New( proof ) )
      val proof_sk = lkNew2Old( proof_sk_new )
      val s = StructCreators.extract( proof_sk )

      val prf = deleteTautologies( proofProfile( s, proof_sk ).map( _.toHOLSequent ) ).asInstanceOf[List[HOLClause]]

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter( "target" + separator + "lattice-prf.tptp" )
      writer_prf.write( tptp_prf )
      writer_prf.flush

      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toHOLSequent ) ).asInstanceOf[List[HOLClause]]
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter( "target" + separator + "lattice-cs.tptp" )
      writer.write( tptp )
      writer.flush

      val prf_cs_intersect = prf.filter( seq => cs.contains( seq ) )

      // refute it with prover9
      Prover9.getRobinsonProof( prf ) match {
        case None      => "" must beEqualTo( "refutation of proof profile failed" )
        case Some( _ ) => true must beEqualTo( true )
      }
      Prover9.getRobinsonProof( cs ) match {
        case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
        case Some( _ ) => true must beEqualTo( true )
      }

      val projs = Projections( proof_sk )
      val path = "target" + separator + "lattice-sk.xml"
      saveXML(
        Tuple2( "lattice-sk", proof_sk ) ::
          projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        // projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2( "cs", cs ) :: Tuple2( "prf", prf ) :: Tuple2( "cs_prf_intersection", prf_cs_intersect ) :: Nil, path
      )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
    }
  }
}
