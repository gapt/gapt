/** 
 * Description: 
**/

package at.logic.integration_tests

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import scala.xml._

import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.lkSpecs.beMultisetEqual
import at.logic.calculi.lk.base._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml.saveXML

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


  "The system" should {
    "parse correctly the second-order prime proof" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime2.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      val proof = proofs.first
      printStats( proof )

      val cut_occs = getCutAncestors( proof )
      val s = StructCreators.extract( proof, cut_occs )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
//      cs.foreach( s => print( sequentToString( s ) + "\n") )
      val dcs = deleteTautologies( cs )
      val css = setNormalize( dcs )
      print("cs size: " + cs.size + "\n")
      print("after tautology deletion: " + dcs.size + "\n")
      print("after set-normalization: " + css.size + "\n")
      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Nil, "target" + separator + "test-classes" + separator + "prime2-cs.xml" )
    }

    "parse correctly the first-order prime proof, n=0" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-0.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      val proof = proofs.first
      val cut_occs = getCutAncestors( proof )
      val s = StructCreators.extract( proof, cut_occs )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
//      cs.foreach( s => print( sequentToString( s ) + "\n") )
      proofs.size must beEqual(1)
      print("cs size: " + cs.size + "\n")
      printStats( proof )
    }

    "parse correctly the first-order prime proof, n=1" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-1.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      val proof = proofs.first
      val cut_occs = getCutAncestors( proof )
      val s = StructCreators.extract( proof, cut_occs )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
//      cs.foreach( s => print( sequentToString( s ) + "\n") )
      proofs.size must beEqual(1)
      print("cs size: " + cs.size + "\n")
      printStats( proof )
    }

    "parse correctly the first-order prime proof, n=2" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime1-2.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      val proof = proofs.first
      val cut_occs = getCutAncestors( proof )
      val s = StructCreators.extract( proof, cut_occs )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
//      cs.foreach( s => print( sequentToString( s ) + "\n") )
      proofs.size must beEqual(1)
      print("cs size: " + cs.size + "\n")
      printStats( proof )
    }
  }
}
