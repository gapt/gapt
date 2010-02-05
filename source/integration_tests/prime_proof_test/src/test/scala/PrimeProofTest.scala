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
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.writers.FileWriter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk._
import at.logic.algorithms.subsumption._
import at.logic.transformations.skolemization.lksk.LKtoLKskc

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

class PrimeProofTest extends SpecificationWithJUnit {

  def sequentToString( s: Sequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toStringSimple + ", ")
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toStringSimple + ", ")
    ret
  }

  def printStats( p: LKProof ) = {
    val stats = getStatistics( p )
    print("unary: " + stats.unary + "\n")
    print("binary: " + stats.binary + "\n")
    print("cuts: " + stats.cuts + "\n")
  }

  def mySort(x: Sequent, y: Sequent) = (x.toString < y.toString) // lexicographically

  "The system" should {
    "parse correctly the second-order prime proof" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime2.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      val proof = proofs.first
      printStats( proof )

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )

      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      Console.println("dcs size: " + dcs.size)
      val css = dcs.removeDuplicates
      Console.println("css size: " + css.size)

      val cssv = sequentNormalize(css)
      Console.println("cssv size: " + cssv.size)
      val neg = cssv.filter(x => x.succedent.isEmpty)
      val mix = cssv.filter(x => !x.succedent.isEmpty && !x.antecedent.isEmpty)
      val pos = cssv.filter(x => x.antecedent.isEmpty)

      (new FileWriter("target" + separator + "test-classes" + separator + "prime2-cs.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
        .exportSequentList(neg.sort(mySort) ++ mix.sort(mySort) ++ pos.sort(mySort)).close
      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Pair("cssv", cssv.toList)::Nil, "target" + separator + "test-classes" + separator + "prime2-cs.xml" )
    }

    "parse correctly the first-order prime proof, n=0" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-0.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      val proof = proofs.first
      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = dcs.removeDuplicates
      Console.println("css: " + css.size)
      val cssv = sequentNormalize(css)
      Console.println("cssv: " + cssv.size)
      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css))::Pair("cssv", cssv)::Nil, "target" + separator + "test-classes" + separator + "prime1-0-cs.xml" )
    }

    "parse correctly the first-order prime proof, n=1" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-1.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      val proof = proofs.first
      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = dcs.removeDuplicates
      Console.println("css: " + css.size)
      val cssv = sequentNormalize(css)
      Console.println("cssv: " + cssv.size)
      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css))::Pair("cssv", cssv)::Nil, "target" + separator + "test-classes" + separator + "prime1-1-cs.xml" )
    }

    "parse correctly the first-order prime proof, n=2" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-2.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      val proof = proofs.first
      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = dcs.removeDuplicates
      Console.println("css: " + css.size)
      val cssv = sequentNormalize(css)
      Console.println("cssv: " + cssv.size)
      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css))::Pair("cssv", cssv)::Nil, "target" + separator + "test-classes" + separator + "prime1-2-cs.xml" )
    }
  }
}
