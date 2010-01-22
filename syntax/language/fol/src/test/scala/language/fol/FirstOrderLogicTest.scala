/*
 * FirstOrderLogicTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.fol

import org.specs._
import org.specs.runner._

import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.typedLambdaCalculus.App

class FirstOrderLogicTest extends SpecificationWithJUnit {
  "FirstOrderLogic" should {
    "construct correctly an atom formula P(x,f(y),c)" in {
      val P = new ConstantStringSymbol( "P" )
      val x = new VariableStringSymbol( "x" )
      val y = new VariableStringSymbol( "y" )
      val f = new ConstantStringSymbol( "f" )
      val c = new ConstantStringSymbol( "c" )
      val Pc = FOLFactory.createVar( P, (i -> (i -> (i -> o))) )
      val fc = FOLFactory.createVar( f, (i -> o) )
      Atom( P, FOLVar(x)::Function(f,FOLVar(y)::Nil)::FOLConst(c)::Nil ) must beLike {
        case App( App( App( Pc, FOLVar(x) ), App( fc, FOLVar(y) ) ), FOLConst(c) ) => true
      }
    }
    "constructs correctly an atom using the factory" in {
      val var3 = Atom(new ConstantStringSymbol("X3"), Nil)
      true
    }
    "constructs currectly an and using the factory" in {
      val var1 = FOLVar(new VariableStringSymbol("x1"))
      val const1 = FOLConst(new ConstantStringSymbol("c1"))
      val var2 = FOLVar(new VariableStringSymbol("x2"))
      val atom1 = Atom(new ConstantStringSymbol("A"),var1::var2::const1::Nil)
      val var3 = Atom(new ConstantStringSymbol("X3"), Nil)
      val and1 = And(atom1, var3)
      true
    }
    "constructs currectly a forall using the factory" in {
      val var1 = FOLVar(new VariableStringSymbol("x1"))
      val const1 = FOLConst(new ConstantStringSymbol("c1"))
      val var2 = FOLVar(new VariableStringSymbol("x2"))
      val atom1 = Atom(new ConstantStringSymbol("A"),var1::var2::const1::Nil)
      val all1 = AllVar(var1, atom1)
      true
    }
  }
}
