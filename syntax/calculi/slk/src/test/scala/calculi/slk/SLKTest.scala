/*
 * SLKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.slk

import org.specs._
import org.specs.runner._

import at.logic.language.schema._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._

class SLKTest extends SpecificationWithJUnit {
  implicit val factory = PointerFOFactoryInstance

  "The calculus SLK" should {
    "work for a simple proof" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val p0 = IndexedPredicate(ConstantStringSymbol("p"), IntZero()::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val ax = Axiom(Sequent(p0::Nil, Nil))
      val proof = AndEquivalenceRule3(ax, ax.root.antecedent.head, f)
      proof.root.getSequent must beEqual( Sequent(f::Nil, Nil ) )
    }
    "work for AndEquivalenceRule1" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val n = IntVar(new VariableStringSymbol("n"))
      val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
      val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
      val and_1_n_ai = BigAnd(i, ai,Succ(IntZero()), n)
      val and_1_sn_ai = BigAnd(i, ai,Succ(IntZero()), Succ(n))
      val ax = Axiom(Sequent(And(and_1_n_ai, a_sn)::Nil,a_sn::Nil))
      val proof = AndEquivalenceRule1(ax, ax.root.antecedent.head, and_1_sn_ai)
      proof.root.getSequent must beEqual( Sequent(and_1_sn_ai::Nil, a_sn::Nil ) )
    }
    "work for OrEquivalenceRule1" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val n = IntVar(new VariableStringSymbol("n"))
      val ai = IndexedPredicate(new ConstantStringSymbol("A"), i::Nil)
      val a_sn = IndexedPredicate(new ConstantStringSymbol("A"), Succ(n)::Nil)
      val or_1_n_ai = BigOr(i, ai, Succ(IntZero()), n)
      val or_1_sn_ai = BigOr(i, ai, Succ(IntZero()), Succ(n))
      val ax = Axiom(Sequent(Or(or_1_n_ai, a_sn)::Nil,a_sn::Nil))
      val proof = OrEquivalenceRule1(ax, ax.root.antecedent.head, or_1_sn_ai)
      proof.root.getSequent must beEqual( Sequent(or_1_sn_ai::Nil, a_sn::Nil ) )
    }
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
      proof.root.getSequent must beEqual( Sequent(or_1_sn_ai::Nil, a_sn::Nil ) )
    }*/
  }
}
