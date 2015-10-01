package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.formats.latex.SequentsListLatexExporter
import at.logic.gapt.formats.arithmetic.HOLTermArithmeticalExporter
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.writers.FileWriter
import at.logic.gapt.proofs.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.ceres.struct.StructCreators

import java.util.zip.GZIPInputStream
import java.io.{ FileReader, FileInputStream, InputStreamReader }
import java.io.File.separator
import org.specs2.mutable._
import org.specs2.execute.Success

class LNPProofTest extends Specification {

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

  sequential
  "The system" should {
    "parse correctly the LNP proof" in {
      val proofs = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "lnp.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase().proofs
      proofs.size must beEqualTo( 1 )
      val proof = proofs.head._2
      //printStats( proof )

      val proof_sk = LKToLKsk( proof )
      val s = StructCreators.extract( proof_sk )

      val cs = StandardClauseSet.transformStructToClauseSet( s ) map ( _.toHOLSequent )
      val dcs = deleteTautologies( cs )
      //Console.println("dcs size: " + dcs.size)
      val css = dcs.distinct
      //Console.println("css size: " + css.size)
      //val cssv = sequentNormalize(css)
      //Console.println("cssv size: " + cssv.size)
      //(new FileWriter("target" + separator + "lnp-cs.tex") with SequentsListLatexExporter
      //  with HOLTermArithmeticalExporter).exportSequentList(cssv.sortWith((x,y) => x.toString < y.toString), List()).close
      saveXML(
        List(),
        List( ( "cs", cs ), ( "dcs", dcs ), ( "css", ( css ) ) //("cssv", (cssv))
        ),
        "target" + separator + "lnp-cs.xml"
      )
      // specs2 require a least one Result, see org.specs2.specification.Example 
      Success()
    }
  }
}
