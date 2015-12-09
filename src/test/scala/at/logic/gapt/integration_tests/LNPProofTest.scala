package at.logic.gapt.integration_tests

import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.lk.deleteTautologies
import at.logic.gapt.proofs.lkNew._
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

  /*
  def printStats( p: LKProof ) = {
    val nLine = sys.props( "line.separator" )
    val stats = getStatistics( p )
    print( "unary: " + stats.unary + nLine )
    print( "binary: " + stats.binary + nLine )
    print( "cuts: " + stats.cuts + nLine )
  }*/

  "The system" should {
    "parse correctly the LNP proof" in {
      val proofs = ( new XMLReader( getClass.getClassLoader.getResourceAsStream( "lnp.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase().proofs
      proofs.size must beEqualTo( 1 )
      val proof = lkOld2New( proofs.head._2 )
      //printStats( proof )

      val proof_sk = skolemize( regularize( proof ) )
      val s = extractStruct( proof_sk )

      val cs = CharacteristicClauseSet( s )
      val css = deleteTautologies( cs )
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
      Prover9.getRobinsonProof( css ) match {
        case Some( rp ) =>
          val proj = Projections( proof_sk )
          val acnf = CERES( proof_sk.endSequent, proj, rp )
          ( acnf.endSequent multiSetEquals proof_sk.endSequent ) must beTrue
        case None =>
          ko( "could not refute css!" )
      }
      // specs2 require a least one Result, see org.specs2.specification.Example 
      ok( "No errors" )
    }
  }
}
