package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.proofs.ceres_omega._
import at.logic.gapt.proofs.lkOld.deleteTautologies
import at.logic.gapt.proofs.lk._
import at.logic.gapt.formats.latex.SequentsListLatexExporter
import at.logic.gapt.formats.arithmetic.HOLTermArithmeticalExporter
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.writers.FileWriter
import at.logic.gapt.proofs.ceres.CharacteristicClauseSet

import java.util.zip.GZIPInputStream
import java.io.{ FileReader, FileInputStream, InputStreamReader }
import java.io.File.separator
import at.logic.gapt.provers.prover9.Prover9
import org.specs2.mutable._
import org.specs2.execute.Success

class LNPProofTest extends Specification {

  "The system" should {
    "parse correctly the LNP proof" in {
      skipped( "This HOL proof does have axioms different from F :- F but CERES_omega is not defined on them." )
      val pdb = XMLProofDatabaseParser( getClass.getClassLoader.getResourceAsStream( "lnp.xml" ) )
      val proofs = pdb.proofs
      proofs.size must beEqualTo( 1 )
      val proof = proofs.head._2
      //printStats( proof )

      val proof_sk = LKToLKsk( regularize( DefinitionElimination( pdb.Definitions )( proof ) ) )
      val s = extractStructFromLKsk( proof_sk )

      val cs = CharacteristicClauseSet( s )
      val css = deleteTautologies( cs )
      css.map( println )
      //Console.println("css size: " + css.size)
      //val cssv = sequentNormalize(css)
      //Console.println("cssv size: " + cssv.size)
      //(new FileWriter("target" + separator + "lnp-cs.tex") with SequentsListLatexExporter
      //  with HOLTermArithmeticalExporter).exportSequentList(cssv.sortWith((x,y) => x.toString < y.toString), List()).close
      saveXML(
        List(),
        List( ( "cs", cs.toList ), ( "css", ( css.toList ) ) //("cssv", (cssv))
        ),
        "target" + separator + "lnp-cs.xml"
      )
      // specs2 require a least one Result, see org.specs2.specification.Example
      ok( "No errors" )
    }
  }
}
