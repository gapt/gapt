/*
 * SLKTest.scala
 *
 */

package at.logic.calculi.slk

import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success

import at.logic.language.schema._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.Axiom
import at.logic.calculi.occurrences._
import at.logic.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class SLKTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory

  "The calculus SLK" should {
    
    "work for a simple proof" in {
      val i = IntVar("i")
      val pi = IndexedPredicate("p", i::Nil)
      val p0 = IndexedPredicate("p", IntZero()::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val ax = Axiom(p0 +: Seq.empty[SchemaFormula], Seq.empty[SchemaFormula])
      val proof = AndEquivalenceRule3(ax, ax.root.antecedent.head, f)
      proof.root.toFSequent must beEqualTo (FSequent( f +: Seq.empty[SchemaFormula], Seq.empty[SchemaFormula]))
    }

    "work for AndEquivalenceRule1" in {
      val i = IntVar("i")
      val n = IntVar("n")
      val ai = IndexedPredicate("A", i::Nil)
      val a_sn = IndexedPredicate("A", Succ(n)::Nil)
      val and_1_n_ai = BigAnd(i, ai,Succ(IntZero()), n)
      val and_1_sn_ai = BigAnd(i, ai,Succ(IntZero()), Succ(n))
      val ax = Axiom(And(and_1_n_ai, a_sn) +: Seq.empty[SchemaFormula], a_sn +: Seq.empty[SchemaFormula])
      val proof = AndEquivalenceRule1(ax, ax.root.antecedent.head, and_1_sn_ai)
      proof.root.toFSequent must beEqualTo (FSequent( and_1_sn_ai +: Seq.empty[SchemaFormula], a_sn +: Seq.empty[SchemaFormula]))

    }
    
    "work for OrEquivalenceRule1" in {
      val i = IntVar("i")
      val n = IntVar("n")
      val ai = IndexedPredicate("A", i::Nil)
      val a_sn = IndexedPredicate("A", Succ(n)::Nil)
      val or_1_n_ai = BigOr(i, ai, Succ(IntZero()), n)
      val or_1_sn_ai = BigOr(i, ai, Succ(IntZero()), Succ(n))
      val ax = Axiom(Or(or_1_n_ai, a_sn) +: Seq.empty[SchemaFormula], a_sn +: Seq.empty[SchemaFormula] )
      val proof = OrEquivalenceRule1(ax, ax.root.antecedent.head, or_1_sn_ai)
      proof.root.toFSequent must beEqualTo (FSequent( or_1_sn_ai +: Seq.empty[SchemaFormula], a_sn +: Seq.empty[SchemaFormula]))

    }
    
    "work for sCutRule" in {
      def f = SchemaConst("f", Ti->Ti)
      def h = SchemaConst("h", ->(Tindex , ->(Ti, Ti)))
      def g = SchemaConst("g", ->(Tindex , ->(Ti, Ti)))
      val k = IntVar("k")
      val x = SchemaVar("x", Ti)
      val base2 = x
      val step2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val base1 = sTerm(g, IntZero(), x::Nil)
      val step1 = sTerm(g, Succ(k), x::Nil)
      dbTRS.clear
      dbTRS.add(g, Tuple2(base1, base2), Tuple2(step1, step2))
      val term1 = sTerm(g, Succ(Succ(k)), x::Nil)
      val term2 = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      val f1 = Atom(SchemaConst("P", term1.exptype -> To), term1::Nil)
      val f2 = Atom(SchemaConst("P", term2.exptype -> To), term2::Nil)

      val ax1  = Axiom(f1::Nil, f1::Nil)
      val ax2  = Axiom(f2::Nil, f2::Nil)
      val cut = sCutRule(ax1, ax2, f1)
      
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
