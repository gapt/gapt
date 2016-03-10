package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.XMLParser
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
import java.io.{ FileInputStream, FileReader, InputStreamReader }
import java.io.File.separator

import at.logic.gapt.examples.primediv
import at.logic.gapt.expr.HOLAtom
import at.logic.gapt.expr.fol.reduceHolToFol
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.spass.SPASS
import org.specs2.mutable._
import org.specs2.execute.Success

class LNPProofTest extends Specification {

  "The system" should {
    "parse correctly the LNP proof" in {
      val proof_sk = LKToLKsk( regularize( AtomicExpansion( DefinitionElimination( primediv.defs )( primediv.proof ) ) ) )
      val s = extractStructFromLKsk( proof_sk )

      val cs = CharacteristicClauseSet( s )
      val css = deleteTautologies( cs )
      css.map( println )
      //Console.println("css size: " + css.size)
      //val cssv = sequentNormalize(css)
      //Console.println("cssv size: " + cssv.size)
      //(new FileWriter("target" + separator + "lnp-cs.tex") with SequentsListLatexExporter
      //  with HOLTermArithmeticalExporter).exportSequentList(cssv.sortWith((x,y) => x.toString < y.toString), List()).close
      //      saveXML(
      //        List(),
      //        List( ( "cs", cs.toList ), ( "css", ( css.toList ) ) //("cssv", (cssv))
      //        ),
      //        "target" + separator + "lnp-cs.xml"
      //      )
      // specs2 require a least one Result, see org.specs2.specification.Example
      ok( "No errors" )
    }
  }

  "prime divisor proof" in { primediv; ok }
}
