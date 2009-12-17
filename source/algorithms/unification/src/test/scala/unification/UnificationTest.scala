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
    }
    "returns a list of all variables (i.e. x::y::Nil) in the term  f(g(x,a),y,b), where a and b are constants " in {
        val t3 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t4 = Function(ConstantStringSymbol("f"), t3::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (alg.getVars(t4)) must beEqual (FOLVar(VariableStringSymbol("x"))::FOLVar(VariableStringSymbol("y"))::Nil)
    }
    "returns a unifier for the pair <z,f(g(x,a),y,b)>, where x,y,z are vars, a and b are consts" in {
        val z = FOLVar(VariableStringSymbol("z"))
        val t5 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t6 = Function(ConstantStringSymbol("f"), t5::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (alg.unify(z, t6)) must beEqual (Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("z")).asInstanceOf[Var], t6)::Nil)))
    }
    "returns the None for the pair <a,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
        val a = FOLConst(ConstantStringSymbol("a"))
        val t7 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t8 = Function(ConstantStringSymbol("f"), t7::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (alg.unify(a, t8)) must beEqual (None)//(Some(Substitution( Nil)))
    }
    "returns the None for the pair <x,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val t7 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t8 = Function(ConstantStringSymbol("f"), t7::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
      //   alg.printSubst(alg.unify(x,t8).get)
        (alg.unify(x, t8)) must beEqual (None)//(Some(Substitution( Nil)))
    }/*
    "returns the unifier {x->b,y->g(b)} for the pair <f(y,b),f(g(x),y)>, where x,y are vars, a and b are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val b = FOLConst(ConstantStringSymbol("b"))
        val c = FOLConst(ConstantStringSymbol("c"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val gb = Function(ConstantStringSymbol("g"),b::Nil)
        val t9 = Function(ConstantStringSymbol("f"), gx::y::Nil)
        val t10 = Function(ConstantStringSymbol("f"), y::gb::Nil)
     
     //this line does not work   alg.printSubst(alg.unify(t9,t10).get)
      //  (alg.unify(t9,t10)) must beEqual (Some(Substitution(SingleSubstitution(x,b) :: SingleSubstitution(y,gb) :: Nil)))
        (alg.unify(c,t10)) must beEqual (None)
    }*/
  }
}