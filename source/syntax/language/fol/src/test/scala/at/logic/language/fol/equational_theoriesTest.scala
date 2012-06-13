package at.logic.language.fol;
/*
package at.logic.language.fol.equations

import org.specs2.mutable._
//import org.specs.runner._

import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import  at.logic.language.hol.logicSymbols._
import org.scalacheck.Prop.Exception

class EquationsTest extends SpecificationWithJUnit {
  "Equations" should {
    "be correctly constructed: " in {
      val x :FOLTerm = FOLVar(VariableStringSymbol("x"))
      val y :FOLTerm = FOLVar(VariableStringSymbol("y"))
      val z :FOLTerm = FOLVar(VariableStringSymbol("z"))
      val plus = ConstantStringSymbol("+")
      val equals = ConstantStringSymbol("=")
      val pred = ConstantStringSymbol("P")
      val leftassoc = Function(plus, List(Function(plus,List(x,y)), z));
      val rightassoc = Function(plus, List(x, Function(plus,List(x,z))));

      val f = Atom(equals,List(leftassoc , rightassoc ))
      val g = Function(equals,List(leftassoc , rightassoc ))
      val p = Atom(pred,List(leftassoc , rightassoc ))

      //println("leftassoc:"+leftassoc)
      //println("rightassoc:"+rightassoc)
      //println("fun:"+f+"  " +f.exptype)

      "x+(y+z) = (x+y)+z is an equation" in {
        val equation : Equation = Equation(f)
        (f.toString()) must beEqualTo (equation toString())
      }

      "P(x+(y+z), (x+y)+z) is not an equation" in {
        var threw_exception = false
        try {
          Equation(p)
        } catch  {
          case _ => threw_exception = true
        }
         threw_exception must beEqualTo(true)
      }


    }
  }

}
 */
