/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lksk

import at.logic.calculi.occurrences.FormulaOccurrence
import base._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols._
import base.LKskFOFactory._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, Axiom => LKAxiom}
import at.logic.calculi.lk.quantificationRules._
import base.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.occurrences.FOFactory
import at.logic.calculi.lk.base.types._

@RunWith(classOf[JUnitRunner])
class LKskTest extends SpecificationWithJUnit {
  val c1 = HOLVar("a", i->o)
  val v1 = HOLVar("x", i)
  val f1 = HOLAppFormula(c1,v1)
  val c2 = HOLVar("b", i->o)
  val v2 = HOLVar("c", i)
  val f2 = HOLAppFormula(c1,v1)
  val f3 = HOLVarFormula("e")
  //val ax = Axiom.createDefault(Sequent(List(new LabelledFormulaOccurrence(f1, Nil, EmptyLabel() )), List(new LabelledFormulaOccurrence(f1, Nil, EmptyLabel() ))), Pair((EmptyLabel() + f2)::Nil, EmptyLabel()::Nil ))
  val ax = Axiom.createDefault(new FSequent(f1::Nil, f1::Nil), Pair((EmptyLabel() + f2)::Nil, EmptyLabel()::Nil ))
  val a1 = ax._1 // Axiom return a pair of the proof and a mapping and we want only the proof here
  //val a2 = (Axiom.createDefault(Sequent(List(new LabelledFormulaOccurrence(f1, Nil, EmptyLabel() )), List(new LabelledFormulaOccurrence(f1, Nil, EmptyLabel() ))), Pair((EmptyLabel() + f2)::Nil, (EmptyLabel() + f3)::Nil) ) )._1
  val a2 = (Axiom.createDefault(new FSequent(f1::Nil, f1::Nil), Pair((EmptyLabel() + f2)::Nil, (EmptyLabel() + f3)::Nil) ) )._1


  "The factories/extractors for LKsk" should {
    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        // TODO: check map!
        a1.root.antecedent.head must beLike {case o : LabelledFormulaOccurrence => ok }
        a1.root.antecedent.head.factory must beLike {case o : FOFactory => ok }
        a1 must beLike {case Axiom(o) => o.antecedent.toArray.apply(0).formula == f1 && o.succedent.toArray.apply(0).formula == f1 must_== true}
      }
    }
    "work for OrLeftRule" in {
      val a = OrLeftRule(a1, a2, f1, f2)
      a.prin.head.factory must beLike {case o : FOFactory => ok }
      a.prin.head must beLike {case o : LabelledFormulaOccurrence => ok }
     // o.skolem_label == (EmptyLabel() + f1)}
    }
  }
}
