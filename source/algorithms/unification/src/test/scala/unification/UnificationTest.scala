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
    "returns the substitution {x->a,y->b} where a and b are constants, x and y are variables" in {
        val t1 = Function(ConstantStringSymbol("f"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t2 = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (alg.unify(t1, t2)) must beEqual (Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil):::Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("y")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("b")).asInstanceOf[LambdaExpression])::Nil)))
       
                                       //(Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil):::Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("y")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("b")).asInstanceOf[LambdaExpression])::Nil)))
    
        //Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("y")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("b")).asInstanceOf[LambdaExpression])::Nil):::Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil))
    } 
    "returns the substitution {x->a} where a is a constant, x is a variable" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val a = FOLConst(ConstantStringSymbol("a"))
        (alg.unify(x, a)) must beEqual (Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil)))

                                       //(Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil):::Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("y")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("b")).asInstanceOf[LambdaExpression])::Nil)))

        //Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("y")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("b")).asInstanceOf[LambdaExpression])::Nil)):::Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil))
    }
  }
}