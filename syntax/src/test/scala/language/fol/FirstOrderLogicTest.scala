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
  }
}
