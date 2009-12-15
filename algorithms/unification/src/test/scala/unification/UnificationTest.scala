/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package at.logic.unification

import org.specs._
import org.specs.runner._
import at.logic.language.fol

class UnificationTest extends SpecificationWithJUnit {
  //val alg = new FOLUnification {}
  "Unification" should {
    "return None if terms are not unifiable" in
    {
      "term 1" in
      {
        var a: FOLConst = FOLConst(ConstantStringSymbol("a"))
        var sym: ConstantSymbolA = ConstantStringSymbol("f")
        var args: List[FOLTerm]
        args = args+a
        var func1 = Function(sym, args)
      }

      "term 2" in
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
}
*/