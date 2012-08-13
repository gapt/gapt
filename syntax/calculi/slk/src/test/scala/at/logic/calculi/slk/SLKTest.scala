/*
 * SLKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.slk

import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

import at.logic.language.schema._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import scala.collection.immutable.Seq
import at.logic.language.hol.HOLVarFormula._
import at.logic.calculi.lk.propositionalRules.NegLeftRule._
import org.specs2.execute.Success
import at.logic.language.hol.HOLConst._
import at.logic.language.lambda.types.Ti._
import at.logic.language.lambda.types.->._
import at.logic.language.lambda.types.Tindex._
import at.logic.language.hol.Definitions._
import at.logic.language.schema.sTerm._
import at.logic.language.lambda.types.{Tindex, ->, Ti}
import at.logic.language.hol.{HOLConst, HOLVar, Atom, HOLVarFormula}

@RunWith(classOf[JUnitRunner])
class SLKTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory

  "The calculus SLK" should {
    "work for a simple proof" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val p0 = IndexedPredicate(ConstantStringSymbol("p"), IntZero()::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val ax = Axiom(p0 +: Seq.empty[SchemaFormula], Seq.empty[SchemaFormula])
      val proof = AndEquivalenceRule3(ax, ax.root.antecedent.head, f)
      proof.root.toFSequent must beEqualTo (FSequent( f +: Seq.empty[SchemaFormula], Seq.empty[SchemaFormula]))
    }

    "work for AndEquivalenceRule1" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val n = IntVar(new VariableStringSymbol("n"))
      val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
      val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
      val and_1_n_ai = BigAnd(i, ai,Succ(IntZero()), n)
      val and_1_sn_ai = BigAnd(i, ai,Succ(IntZero()), Succ(n))
      val ax = Axiom(And(and_1_n_ai, a_sn) +: scala.collection.immutable.Seq.empty[SchemaFormula], a_sn +: scala.collection.immutable.Seq.empty[SchemaFormula])
      val proof = AndEquivalenceRule1(ax, ax.root.antecedent.head, and_1_sn_ai)
      proof.root.toFSequent must beEqualTo (FSequent( and_1_sn_ai +: Seq.empty[SchemaFormula], a_sn +: Seq.empty[SchemaFormula]))

    }
    "work for OrEquivalenceRule1" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val n = IntVar(new VariableStringSymbol("n"))
      val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
      val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
      val or_1_n_ai = BigOr(i, ai, Succ(IntZero()), n)
      val or_1_sn_ai = BigOr(i, ai, Succ(IntZero()), Succ(n))
      val ax = Axiom(Or(or_1_n_ai, a_sn) +: scala.collection.immutable.Seq.empty[SchemaFormula], a_sn +: scala.collection.immutable.Seq.empty[SchemaFormula] )
      val proof = OrEquivalenceRule1(ax, ax.root.antecedent.head, or_1_sn_ai)
      proof.root.toFSequent must beEqualTo (FSequent( or_1_sn_ai +: Seq.empty[SchemaFormula], a_sn +: Seq.empty[SchemaFormula]))

    }
    "work for sCutRule" in {
      def f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
      def h = HOLConst(new ConstantStringSymbol("h"), ->(Tindex() , ->(Ti(), Ti())))
      def g = HOLConst(new ConstantStringSymbol("g"), ->(Tindex() , ->(Ti(), Ti())))
      val k = IntVar(new VariableStringSymbol("k"))
      val x = hol.createVar(new VariableStringSymbol("x"), Ti(), None).asInstanceOf[HOLVar]
      val base = x
      val step = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val db = dbTRS(g, base, step)
      val term1 = sTerm(g, Succ(Succ(k)), x::Nil)
      val term2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      println("\n\nterm1 = "+unfoldSTerm(term1, db))
      println("term2 = "+unfoldSTerm(term2, db))
      val f1 = Atom(new ConstantStringSymbol("P"), term1::Nil)
      val f2 = Atom(new ConstantStringSymbol("P"), term2::Nil)
      println("\n\nf1 = "+unfoldSFormula(f1, db))
      println("f2 = "+unfoldSFormula(f2, db))

      val ax1  = Axiom(f1::Nil, f1::Nil)
      val ax2  = Axiom(f2::Nil, f2::Nil)
      val cut = sCutRule(ax1, ax2, f1, db)
      println("\n\nroot = "+cut.root)
      Success()
    }
    /*
    // TODO: fix this test!
    "have a correct SchemaProofLinkRule extractor" in {
      val p0 = IndexedPredicate(new ConstantStringSymbol("p"), IntZero()::Nil)
      val link = SchemaProofLinkRule(Sequent( p0::Nil, p0::Nil ), "varphi", Nil )
      link must beLike {
        case SchemaProofLinkRule(s, n, i) => {
          val a = s match { case Sequent(x::Nil, y::Nil) if (x == p0 && y == p0) => true }
          val b = n == "varphi"
          val c = i == IntZero()
          a && b && c
        }
      }
    } */
  /*  // the following test fails because the position occurrences
      // do not distinguish left/right side of the sequent, only
      // the position inside the antecedent/succedent!

      "work for OrEquivalenceRule1 using position occurrences" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val n = IntVar(new VariableStringSymbol("n"))
      val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
      val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
      val or_1_n_ai = BigOr(i, ai, Succ(IntZero()), n)
      val or_1_sn_ai = BigOr(i, ai, Succ(IntZero()), Succ(n))
      val ax = Axiom(Sequent(Or(or_1_n_ai, a_sn)::Nil,a_sn::Nil))(PositionsFOFactory)
      val proof = OrEquivalenceRule1(ax, ax.root.antecedent.head, or_1_sn_ai)
      proof.root.getSequent must beEqualTo( Sequent(or_1_sn_ai::Nil, a_sn::Nil ) )
    }*/
  }
}
