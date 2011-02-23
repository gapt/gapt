package at.logic.integration_tests


import at.logic.parsing.writers.FileWriter
import at.logic.parsing.calculi.latex._
import at.logic.parsing.language.arithmetic._
import at.logic.calculi.occurrences._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.calculi.lk.macroRules._
import at.logic.parsing.calculi.latex._


import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.writers.FileWriter
import at.logic.calculi.lk.macroRules.AndLeftRule
import at.logic.calculi.lk.base._
import at.logic.language.schema._
import at.logic.calculi.slk._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.occurrences._
import at.logic.transformations.ceres.struct._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import java.io.File.separator

//import at.logic.language.hol._
import org.specs._
import at.logic.calculi.slk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.hol.logicSymbols._
import at.logic.language.schema._
import at.logic.transformations.ceres.struct._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.utils.ds.Multisets._

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

//import java.util.zip.GZIPInputStream
//import java.io.{FileReader, FileInputStream, InputStreamReader}
//import java.io.File.separator


class SchemaTest extends SpecificationWithJUnit {
  implicit val factory = new PointerFOFactory

  //phi_0

  val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
  val A1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(IntZero()))
  val i = IntVar(new VariableStringSymbol("i"))
  val Asi = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))

  val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)

  val ax0 = Axiom(Sequent(A0::Nil, A0::Nil))
  val ax00 = Axiom(Sequent(A0::Nil, A0::Nil))
  val ax1 = Axiom(Sequent(A1::Nil, A1::Nil))
  val ax11 = Axiom(Sequent(A1::Nil, A1::Nil))

  val neglrule = NegLeftRule(ax0, A0)

  val orlr = OrLeftRule(neglrule, ax1, Neg(A0), A1)

  val phi_0 = AndEquivalenceRule3(orlr, Or(Neg(A0), A1), BigAnd(i, Or(Neg(Ai), Asi), IntZero(), IntZero()))


  ////////////////////////////////////////////////////////////////////////////////
  val k = IntVar(new VariableStringSymbol("k"))

  val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
  val Ask = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
  val Assk = IndexedPredicate(new ConstantStringSymbol("A"), Succ(Succ(k)))
//  val A = SchemaFactory.createVar( sym, ->(Tindex(), To()))



  // phi_{k+1}

  val seq_phi = Sequent( A0::BigAnd(i, Or(Neg(Ai), Asi), IntZero(), k)::Nil, Ask::Nil)

  val negAiOrAsi = Or(Neg(Ai), Asi)

  val psi_k1 = SchemaProofLinkRule(Sequent(A0::BigAnd(i, negAiOrAsi, IntZero(), Succ(k))::Nil, BigAnd(i, Ai, IntZero(), Succ(Succ(k)))::Nil), "\\psi", Succ(k)::Nil)
//  val psi_step = SchemaProofLinkRule(Sequent(A0::BigAnd(i, negAiOrAsi, IntZero(), Succ(k))::Nil, BigAnd(i, Ai, IntZero(), Succ(Succ(k)))::Nil), "psi", Succ(k)::Nil)

  val ax3 = Axiom(Sequent(Assk::Nil, Assk::Nil))

//  val weaklrule = WeakeningLeftRule(ax3, BigAnd(i, Ai, IntZero(), k))

  val andlrule = AndLeft2Rule(ax3, BigAnd(i, Ai, IntZero(), Succ(k)), Assk)

  val eq1rule = AndEquivalenceRule1(andlrule, And(BigAnd(i, Ai, IntZero(), Succ(k)), Assk), BigAnd(i, Ai, IntZero(), Succ(Succ(k))))

  val phi_step = CutRule(psi_k1, eq1rule, BigAnd(i, Ai, IntZero(), Succ(Succ(k))))

//  println("\n\n phi_k = "+cutrule.root.getSequent.toStringSimple)

//  val phi_step = SchemaProofLinkRule(Sequent(A0::BigAnd(i, negAiOrAsi, IntZero(), Succ(k))::Nil, Assk::Nil), "\\varphi", Succ(k))


  val seq_psi = Sequent( A0::BigAnd(i, Or(Neg(Ai), Asi), IntZero(), k)::Nil, BigAnd(i, Ai, IntZero(), Succ(k))::Nil)

  // psi_0

  val addbigr =  AndRightEquivalenceRule3(ax00, A0, BigAnd(i, Ai, IntZero(), IntZero()))

  val andrrule = AndRightRule(addbigr, ax11, BigAnd(i, Ai, IntZero(), IntZero()), A1)

  val cutrule1 = CutRule(phi_0, andrrule, A1)

  val contrlr = ContractionLeftRule(cutrule1, A0)

  val psi_0 = AndEquivalenceRule1(contrlr, And(BigAnd(i, Ai, IntZero(), IntZero()), A1), BigAnd(i, Ai, IntZero(), Succ(IntZero())))


  // psi_{k+1}



  val ax4 = Axiom(Sequent(Assk::Nil, Assk::Nil))

  val ax33 = Axiom(Sequent(Ask::Nil, Ask::Nil))

  val neglrule1 = NegLeftRule(ax33, Ask)

  val orlrule = OrLeftRule(neglrule1, ax4, Neg(Ask), Assk)

  val psi_k = SchemaProofLinkRule(seq_psi, "\\psi", k::Nil)

  val andrrule1 = AndRightRule(psi_k, orlrule, BigAnd(i, Ai, IntZero(), Succ(k)), Assk)

  val equiv1rule = AndEquivalenceRule1(andrrule1, And(BigAnd(i, Ai, IntZero(), Succ(k)), Assk), BigAnd(i, Ai, IntZero(), Succ(Succ(k))))

  val phi_k = SchemaProofLinkRule(seq_phi, "\\varphi", k)

  val cutrule2 = CutRule(phi_k, equiv1rule, Ask)

  val contrlrule1 = ContractionLeftRule(cutrule2,  BigAnd(i, Or(Neg(Ai), Asi), IntZero(), k))

  val contrlrule2 = ContractionLeftRule(contrlrule1, A0)

  val andlrule1 = AndLeftRule(contrlrule2, BigAnd(i, Or(Neg(Ai), Asi), IntZero(), k), Or(Neg(Ask), Assk))

  val psi_kplus1 = AndEquivalenceRule1(andlrule1, And(BigAnd(i, Or(Neg(Ai), Asi), IntZero(), k), Or(Neg(Ask), Assk)), BigAnd(i, Or(Neg(Ai), Asi), IntZero(), Succ(k)))


  //------------------------------------------------------------------------------------------------

  SchemaProofDB.clear
  SchemaProofDB.put( new SchemaProof( "\\varphi", k::Nil, seq_phi, phi_0, phi_step ))


  SchemaProofDB.put( new SchemaProof( "\\psi", k::Nil, seq_psi, psi_0, psi_kplus1) )


  val n = IntVar(new VariableStringSymbol("n"))
  val cs = StandardClauseSet.transformStructToClauseSet(StructCreators.extractStruct( "\\varphi", n))

  (new FileWriter("target" + separator + "test-classes" + separator + "cs-varphi.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(cs.map(so => so.getSequent), Nil).close 

  // prune the clause set as in "Computing the characteristic clause set (Nov. 29, 2010)
  val m_empty = HashMultiset[SchemaFormula]()
  val cc0 = (m_empty, m_empty)
  val cc1varphi = (m_empty, m_empty + Ask)
  val cc1psi = (m_empty, m_empty + BigAnd(i, Ai, IntZero(), Succ(k)))
  
  val cs_pruned = cs.filter( s => !(s.antecedent ++ s.succedent).exists( fo => fo.formula match {
    case IndexedPredicate(pred, _) => pred.name match {
      case sym : ClauseSetSymbol => sym.cut_occs != cc1varphi && sym.cut_occs != cc1psi && sym.cut_occs != cc0
      case _ => false
    }
    case _ => false
  } ) )

  (new FileWriter("target" + separator + "test-classes" + separator + "cs-varphi-pruned.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(cs_pruned.map(so => so.getSequent), Nil).close

}
