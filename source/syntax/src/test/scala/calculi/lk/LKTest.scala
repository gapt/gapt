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

class LKTest extends SpecificationWithJUnit {
  "LK factories and extractors" should {
    "work for Axioms" in {
        val c1 = Var("a", i->o, hol)
        val v1 = Var("x", i, hol)
        val f1 = App(c1,v1).asInstanceOf[Formula]
        val f2 = App(c1,v1).asInstanceOf[Formula]
        val a1: LKProof = Axiom(Sequent(f1::Nil, f2::Nil))
        (a1) must beLike {case Axiom(x) => true}
    }
    /*"work for AndRightRule" in {
        val c1 = Var[HOL]("a", i->o)
        val v1 = Var[HOL]("x", i)
        val f1 = App(c1,v1).asInstanceOf[Formula[HOL]]
        val a1 = Axiom(Sequent(f1::Nil, f1::Nil))
        val a2 = Axiom(Sequent(f1::Nil, f1::Nil))
        (AndRightRule(a1, a2, f1, f1)) must beLike {case AndRightRule(a1, a2, x, aux1, aux2, prin1) => true}
    }*/
  }
  "LK rules convenient factories (taking the first formulas)" should {
      "create the correct proof for Contractions" in {
          
      }
  }
}
