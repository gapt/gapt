/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package at.logic.unification

import org.specs._
import org.specs.runner._
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._

class UnificationTest extends SpecificationWithJUnit {
  val alg = new FOLUnification {}
  "Unification" should {
    "return None if terms are not unifiable" in
    {
      "- both are constants" in
      {
        val a = FOLConst(ConstantStringSymbol("a"))
        val b = FOLConst(ConstantStringSymbol("b"))
        (alg.unify(a,b)) must beEqual (None)
      }
      "- both are functions" in {
        val a = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::Nil)
        val b = Function(ConstantStringSymbol("g"), FOLConst(ConstantStringSymbol("a"))::Nil)
        (alg.unify(a,b)) must beEqual (None)
      }
    }
    "return Empty substitution if both terms are" in {
      "constants" in {
        val a = FOLConst(ConstantStringSymbol("a"))
        val b = FOLConst(ConstantStringSymbol("a"))
        (alg.unify(a,b)) must beEqual (Some(Substitution(Nil)))
      }
      "functions" in {
        val a = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::Nil)
        val b = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::Nil)
        (alg.unify(a,b)) must beEqual (Some(Substitution(Nil)))
      }
    }
  }
}
      /*"term 2" in
      {
        var b: FOLConst = FOLConst(ConstantStringSymbol("b"))
        var sym: ConstantSymbolA = ConstantStringSymbol("f")
        var args: List[FOLTerm]
        args = args+b
        var func2 = Function(sym, args)
      }
      val unif: FOLUnification = new FOLUnification(func1,func2)
      unif.unify(func1,func2) must beEqual(NULL)
    }
    "return an empty unifier if terms are unifiable but identical" in {
      "term 1" in {

      }
    }
    "return None if there is an occur check" in {
      "term 1" in {

      }
      "term 2" in {

      }
    }
    "return None if there is a symbol clash" in {
      "term 1" in {

      }
    }
    "should throw an exception if higher order terms are given" in {
      () must throw
    }
  }
}*/
