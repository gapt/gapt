/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lksk

import org.specs._
import org.specs.runner._

import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols._
import propositionalRules._
import base._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.symbols.ImplicitConverters._
import scala.collection.immutable._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.Sequent
import base.TypeSynonyms._

class LKTest extends SpecificationWithJUnit {
  val c1 = HOLVar("a", i->o)
  val v1 = HOLVar("x", i)
  val f1 = HOLAppFormula(c1,v1)
  val c2 = HOLVar("b", i->o)
  val v2 = HOLVar("c", i)
  val f2 = HOLAppFormula(c1,v1)
  val f3 = HOLVarFormula("e")
  val ax = Axiom(Sequent(f1::Nil, f1::Nil), Pair((EmptyLabel() + f2)::Nil, EmptyLabel()::Nil ))
  val a1 = ax._1 // Axiom return a pair of the proof and a mapping and we want only the proof here
  val a2 = (Axiom(Sequent(f1::Nil, f1::Nil), Pair((EmptyLabel() + f2)::Nil, (EmptyLabel() + f3)::Nil) ) )._1

  "The factories/extractors for LKsk" should {

    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        // TODO: check map!
        (a1) must beLike {case Axiom(LabelledSequentOccurrence(x,y,m)) => (x.toArray(0).formula == f1) && (y.toArray(0).formula == f1)}
      }
    }
/*
    "work for OrLeftRule" in {
      val a = OrLeftRule(a1, a2, f1, f2)
      a.root must beLike {case LabelledSequentOccurrence(x,y,m) => m.apply( a.prin.first ) == (new EmptySet + f1)}
    }
*/
  }
}
