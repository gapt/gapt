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

class SLKTest extends SpecificationWithJUnit {
  // implicits for using positions as occurrences
  import at.logic.calculi.occurrences.positions._

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
  }
}
