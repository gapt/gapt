package at.logic.simple_schema_test

import _root_.at.logic.language.hol.HOLFormula
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.writers.FileWriter
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkSpecs._
import at.logic.language.schema._
import at.logic.calculi.slk._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.occurrences._
import at.logic.transformations.ceres.struct._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.utils.ds.Multisets._
import scala.collection.immutable.Seq
import at.logic.transformations.ceres.projections._

import java.io.File.separator

import org.specs.SpecificationWithJUnit

class sCSunfoldTest extends SpecificationWithJUnit {
  def f2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Nil)
  def fseq2seq(ant : Seq[HOLFormula], succ : Seq[HOLFormula]) = Sequent(ant map f2occ , succ map f2occ)

  "SchemaClauseSetTest" should {

    //--  Create LKS proof (Alex's example) --//

    //-- Some formula definitions
    val i = IntVar(new VariableStringSymbol("i"))
    val n = IntVar(new VariableStringSymbol("k"))
    val n1 = Succ(IntVar(new VariableStringSymbol("k")))
    val n2 = Succ(n1);val n3 = Succ(n2)

    val k = IntVar(new VariableStringSymbol("n"))
    val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
    val ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
    val a0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
    val a1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
    val a2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
    val an = IndexedPredicate(new ConstantStringSymbol("A"), n)
    val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), n1)
    val a_ssn = IndexedPredicate(new ConstantStringSymbol("A"), n2)
    val a_sssn = IndexedPredicate(new ConstantStringSymbol("A"), n3)
    val ak = IndexedPredicate(new ConstantStringSymbol("A"), n)
    val ak1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
    val ak2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
    val ak3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)

    val and_1_1_ai = BigAnd(i, ai, one, one)
    val and_0_1_ai = BigAnd(i, ai, zero, one)
    val or_1_1_ai = BigOr(i, ai, one, one)
    val and_1_2_ai = BigAnd(i, ai, one, two)

    val or_1_k1_ai = BigOr(i, ai, one, n1)
    val or_1_k2_ai = BigOr(i, ai, one, n2)
    val and_1_k2_ai = BigAnd(i, ai, one, n2)
    val and_1_k3_ai = BigAnd(i, ai, one, n3)

    val and_0_n_ai = BigAnd(i, ai,IntZero(), n)
    val and_0_k1_ai = BigAnd(i, ai,IntZero(), Succ(n))
    val and_0_ssn_ai = BigAnd(i, ai,IntZero(), Succ(Succ(n)))
    val and_0_sssn_ai = BigAnd(i, ai,IntZero(), Succ(Succ(Succ(n))))
    val or_0_0_not_ai = BigOr(i, Neg(ai), IntZero(), IntZero())
    val or_0_1_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(IntZero()))
    val or_0_n_not_ai = BigOr(i, Neg(ai), IntZero(), n)
    val or_0_sn_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(n))
    val or_0_ssn_not_ai = BigOr(i, Neg(ai), IntZero(), Succ(Succ(n)))
    // end of formula definitions --//


    "construct correct schema proof" in {

      val ax1 = Axiom(a1::Nil, a1::Nil)
      val eq3 = AndLeftEquivalenceRule3(ax1, a1, and_1_1_ai)
      val eq4 = OrRightEquivalenceRule3(eq3, a1, or_1_1_ai)
      val andl1 = AndLeft1Rule(eq4, and_1_1_ai, a2)
      val wr1 = WeakeningRightRule(andl1, a2)
      val andl = AndLeftEquivalenceRule1(wr1, And(and_1_1_ai, a2), and_1_2_ai)
//      val andl = AndLeftEquivalenceRule1(wr1, andl1.root.antecedent.head.formula.asInstanceOf[SchemaFormula], and_1_2_ai)
      val phi0 = andl

      val ax2 = SchemaProofLinkRule(FSequent(and_1_k2_ai::Nil, or_1_k1_ai::ak2::Nil), "\\phi", n::Nil)
                    val ax3 = Axiom(ak2::Nil, ak2::Nil)
                    val wl3 = WeakeningLeftRule(ax3, ak3)
            val cut1 = CutRule(ax2, wl3, ak2)
            val wr3 = WeakeningRightRule(cut1, and_1_k2_ai)
                                                     val ax4 = SchemaProofLinkRule(FSequent(and_1_k2_ai::Nil, or_1_k1_ai::ak2::Nil), "\\phi", n::Nil)
                                  val cut2 = CutRule(wr3, ax4, and_1_k2_ai)
                                  val contr1 = ContractionRightRule(cut2, ak2)
                                  val contr2 = ContractionRightRule(contr1, or_1_k1_ai)
                                  val andll = AndLeftRule(contr2, and_1_k2_ai, ak3)
                                  val biga = AndLeftEquivalenceRule1(andll, And(and_1_k2_ai, ak3), and_1_k3_ai)
                                  val orr = OrRightRule(biga, or_1_k1_ai, ak2)
                                  val wrr = WeakeningRightRule(orr, ak3)
                                  val bigo = OrEquivalenceRule1(wrr, Or(or_1_k1_ai, ak2), or_1_k2_ai)

      val phin = bigo

      printSchemaProof(phin)


    }
  }
}
