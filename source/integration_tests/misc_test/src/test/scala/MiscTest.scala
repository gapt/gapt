/** 
 * Description: 
**/

package at.logic.integration_tests

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

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

import at.logic.transformations.skolemization.lksk.LKtoLKskc
import scala.collection.immutable.EmptySet

/*class MiscTest extends SpecificationWithJUnit {

  "The system" should {
    "parse, skolemize, extract clause set for a simple induction proof" in {
      val proofs = (new XMLReader(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "simple_ind.xml"))) with XMLProofDatabaseParser)..getProofDatabase()
      proofs.size must beEqual(1)
      val proof = proofs.first
      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = setNormalize( dcs )
      val cs_path = "target" + separator + "test-classes" + separator + "simple_ind-cs.xml"
      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Nil, cs_path )
      (new java.io.File( cs_path ) ).exists() must beEqual( true )
    }
  }
}*/
