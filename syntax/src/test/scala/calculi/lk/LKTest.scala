/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import org.specs._
import org.specs.runner._

import at.logic.language.hol.HigherOrderLogic._
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.lambda.Types._
import at.logic.language.lambda.Symbols._
import LK._
import at.logic.language.hol.LogicSymbols.LogicSymbolsDefaultConverters._
import at.logic.language.lambda.Types.TAImplicitConverters._

import scala.collection.immutable._

class LKTest extends Specification with JUnit {
  "LK" should {
    "Axioms build and extract correctly" in {
        val c1 = Var[HOL]("a", i->o)
        val v1 = Var[HOL]("x", i)
        val f1 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val f2 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val a1 = Axiom(HashSet(f1), HashSet(f2))
        (a1) must beLike {case Axiom(x) => true}
    }
    "AndRightRule build and extract correctly" in {
        val c1 = Var[HOL]("a", i->o)
        val v1 = Var[HOL]("x", i)
        val f1 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val f2 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val f3 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val f4 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val a1 = Axiom(HashSet(f1), HashSet(f2))
        val a2 = Axiom(HashSet(f3), HashSet(f4))
        (AndRightRule(a1, a2, a1.root.succedent.elements.next, a2.root.succedent.elements.next)) must beLike {case AndRightRule(a1, a2, x, aux1, aux2, p1) => true}
    }
  }
}
