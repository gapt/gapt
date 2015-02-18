package at.logic.gapt.integration_tests

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.algorithms.{getStatistics, deleteTautologies}
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.io.calculi.latex.SequentsListLatexExporter
import at.logic.gapt.io.calculus.xml.saveXML
import at.logic.gapt.io.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.gapt.io.language.xml.XMLParser._
import at.logic.gapt.io.readers.XMLReaders._
import at.logic.gapt.io.writers.FileWriter
import at.logic.gapt.proofs.algorithms.ceres.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.algorithms.ceres.struct.StructCreators
import at.logic.gapt.proofs.algorithms.skolemization.lksk.LKtoLKskc

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class LNPProofTest extends SpecificationWithJUnit {

  def sequentToString( s: Sequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toString + ", ")
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toString + ", ")
    ret
  }

  def printStats( p: LKProof ) = {
    val stats = getStatistics( p )
    print("unary: " + stats.unary + "\n")
    print("binary: " + stats.binary + "\n")
    print("cuts: " + stats.cuts + "\n")
  }

  sequential
  "The system" should {
    "parse correctly the LNP proof" in {
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("lnp.xml"))) with XMLProofDatabaseParser).getProofDatabase().proofs
      proofs.size must beEqualTo(1)
      val proof = proofs.head._2
      //printStats( proof )

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )

      val cs = StandardClauseSet.transformStructToClauseSet( s ) map (_.toFSequent)
      val dcs = deleteTautologies( cs )
      //Console.println("dcs size: " + dcs.size)
      val css = dcs.distinct
      //Console.println("css size: " + css.size)
      //val cssv = sequentNormalize(css)
      //Console.println("cssv size: " + cssv.size)
      //(new FileWriter("target" + separator + "lnp-cs.tex") with SequentsListLatexExporter
      //  with HOLTermArithmeticalExporter).exportSequentList(cssv.sortWith((x,y) => x.toString < y.toString), List()).close
      saveXML( List(),
              List(("cs", cs), ("dcs", dcs), ("css", (css)) 
              //("cssv", (cssv))
              ),
              "target" + separator + "lnp-cs.xml" )
      // specs2 require a least one Result, see org.specs2.specification.Example 
      Success()
    }
  }
}
