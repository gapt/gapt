/** 
 * Description: 
**/
package at.logic.integration_tests

import _root_.at.logic.transformations.ceres.clauseSets.profile. {printStruct, proofProfile}
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

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.projections.Projections
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.algorithms.fol.hol2fol._
import at.logic.language.fol._



class TapeTest extends SpecificationWithJUnit {
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
    "parse and skolemize the tape proof" in {
      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "tape-in.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqual(1)
      val proof = proofdb.proofs.head._2

      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )


      val sp = at.logic.transformations.ceres.clauseSets.profile.StructCreators.extract( proof_sk )
//      (new proofProfile(proof_sk)).transformStructToProfile(sp)
//      val prf = printStruct(new proofProfile(proof_sk).normalize(sp)))
      println("\n\nsp = "+printStruct(sp))
      //println("\n\ns = " +printStruct(s))
      val normprf = (new proofProfile(proof_sk)).normalize(sp)
      val prf = (new proofProfile(proof_sk)).clausify(normprf).map( so => so.getSequent )
      println("\n\npfl = "+printStruct(normprf))


      val cs = StandardClauseSet.transformStructToClauseSet( s ).map( so => so.getSequent )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter("target" + separator + "test-classes" + separator + "tape-cs.tptp")
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "test-classes" + separator + "tape-sk.xml"
      saveXML( Pair("tape-sk", proof_sk) ::
        projs.map( p => p._1 ).toList.zipWithIndex.map( p => Pair( "\\psi_{" + p._2 + "}", p._1 ) ),
        Pair("cs", cs)::Pair("prf", prf)::Nil, path )
      (new java.io.File( path ) ).exists() must beEqual( true )
    }
  }
}
