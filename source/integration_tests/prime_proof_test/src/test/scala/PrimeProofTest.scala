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
import at.logic.provers.atp.Prover
import at.logic.provers.atp.commands._
import at.logic.provers.atp.refinements.UnitRefinement
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.propositions._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.fol.FOLFormula

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.algorithms.subsumption._
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.algorithms.fol.hol2fol._

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

import scala.collection.mutable.Map

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
      val pdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "prime2.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      pdb.proofs.size must beEqual(1)
      val proof = pdb.proofs.first
      printStats( proof )

      val proof_sk = LKtoLKskc( proof )
      val s = StructCreators.extract( proof_sk )

      val csPre = StandardClauseSet.transformStructToClauseSet(s)
      
      // we will add three axioms: 0 < p(x), 1 < p(x), x = x
      val seq1 = Sequent(Nil, Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("0"), Ti())::Function(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
      val seq2 = Sequent(Nil, Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("1"), Ti())::Function(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
      val seq3 = Sequent(Nil, Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLVar(VariableStringSymbol("x"), Ti())::Nil))::Nil)
      val seq4 = Sequent(Nil, Atom(ConstantStringSymbol("="), Function(ConstantStringSymbol("+"), HOLConst(ConstantStringSymbol("0"), Ti())::HOLVar(VariableStringSymbol("x"), Ti())::Nil, Ti())::HOLVar(VariableStringSymbol("x"), Ti())::Nil)::Nil)

      val holcs = pdb.axioms ::: ( seq1::seq2::seq3::seq4::Nil ) ::: csPre

      // maps original types and definitions of abstractions
      val sectionsPre = ("Types", getTypeInformation(holcs).toList.sort((x,y) => x.toString < y.toString))::Nil

      // convert to fol and obtain map of definitons
      val imap = Map[at.logic.language.lambda.typedLambdaCalculus.LambdaExpression, at.logic.language.hol.logicSymbols.ConstantStringSymbol]()
      val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
      val cs = holcs.map(x => Sequent(
          x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[HOLTerm],imap,iid).asInstanceOf[FOLFormula]),
          x.succedent.map(y => reduceHolToFol(y.asInstanceOf[HOLTerm],imap,iid).asInstanceOf[FOLFormula])
      ))
      val sections = ("Definitions", imap.toList.map(x => (x._1, createExampleFOLConstant(x._1, x._2))))::sectionsPre

      val dcs = deleteTautologies( cs )
      Console.println("dcs size: " + dcs.size)
      val css = dcs.removeDuplicates
      Console.println("css size: " + css.size)

      val cssUnit = simpleUnitResolutionNormalization(css)
      Console.println("cssUnit size: " + cssUnit.size)

      val scss = subsumedClausesRemoval(cssUnit)
      Console.println("scss size: " + scss.size)

      val cssv = sequentNormalize(scss)
      Console.println("cssv size: " + cssv.size)

      // apply unit resolution and subsumption on the resulted clause set
      val ref = new at.logic.provers.atp.refinements.UnitRefinement{}
      new Prover{}.refute(AutomatedFOLStream(cssv.map(x => at.logic.calculi.resolution.base.Clause(x.antecedent.asInstanceOf[List[HOLFormula]], x.succedent.asInstanceOf[List[HOLFormula]])), -1, ref))
      val newUnitSet = ref.clauses.map(x => x.root).toList
      Console.println("newUnitSet size: " + newUnitSet.size)
      val newUnitSetSubsum = subsumedClausesRemoval(newUnitSet)
      Console.println("newUnitSetSubsum size: " + newUnitSetSubsum.size)

      // done for preserving order
      val neg = cssv.filter(x => x.succedent.isEmpty)
      val mix = cssv.filter(x => !x.succedent.isEmpty && !x.antecedent.isEmpty)
      val pos = cssv.filter(x => x.antecedent.isEmpty)

      // done for preserving order
      val neg2 = newUnitSetSubsum.filter(x => x.succedent.isEmpty)
      val mix2 = newUnitSetSubsum.filter(x => !x.succedent.isEmpty && !x.antecedent.isEmpty)
      val pos2 = newUnitSetSubsum.filter(x => x.antecedent.isEmpty)

      val subsum = sequentNormalize(cssUnit).diff(cssv)
      Console.println("subsum size: " + subsum.size)
      (new FileWriter("target" + separator + "test-classes" + separator + "prime2-cs-subsumed.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
        .exportSequentList(subsum, sections).close
      (new FileWriter("target" + separator + "test-classes" + separator + "prime2-cs.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
        .exportSequentList(neg.sort(mySort) ++ mix.sort(mySort) ++ pos.sort(mySort), sections).close
      (new FileWriter("target" + separator + "test-classes" + separator + "prime2-cs-unit.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
        .exportSequentList(neg2.sort(mySort) ++ mix2.sort(mySort) ++ pos2.sort(mySort), sections).close
      //saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Pair("cssv", cssv.toList)::Nil, "target" + separator + "test-classes" + separator + "prime2-cs.xml" )
      //saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Pair("cssv", cssv.toList)::Nil, "target" + separator + "test-classes" + separator + "prime2-cs.xml" )
    }
    /*"parse correctly the first-order prime proof, n=0" in {
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
    }*/
  }
}
