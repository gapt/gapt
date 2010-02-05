/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package at.logic.algorithms.unification

import org.specs._
import org.specs.runner._
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.fol.substitutions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol._
//import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.language.simple._
import at.logic.parsing.readers.StringReader
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

class UnificationTest extends SpecificationWithJUnit {
  private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser
  
  "FOL Unification" should {
    "unify the terms" in {
      "P(x_1), P(x_2)" in {
        val px1 = new MyParser("P(x_1)").getTerm.asInstanceOf[FOLExpression]
        val px2 = new MyParser("P(x_2)").getTerm.asInstanceOf[FOLExpression]
        (FOLUnificationAlgorithm.unify(px1,px2)) must 
          beEqual (Some(Substitution(FOLVar(VariableStringSymbol("x_1")), FOLVar(VariableStringSymbol("x_2")))))

      }
    }
  }
  /*
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
        (alg.unify(x, t8)) must beEqual (None)//(Some(Substitution( Nil)))
    }
    
    "return None for the pair <f(g(c),y), f(y,g(b))> where x,y are vars, a,c are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val b = FOLConst(ConstantStringSymbol("b"))
        val c = FOLConst(ConstantStringSymbol("c"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val gb = Function(ConstantStringSymbol("g"),b::Nil)
        val gc = Function(ConstantStringSymbol("g"),c::Nil)
        val f_gc_y = Function(ConstantStringSymbol("f"), gc::y::Nil)
        val t_y_gb = Function(ConstantStringSymbol("f"), y::gb::Nil)
       (alg.unify(f_gc_y, t_y_gb)) must beEqual (None)
    }

    "returns the unifier {y->g(b), x->b} for the pair <f(g(x),y), f(y,g(b))> where x,y are vars, a and b are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val b = FOLConst(ConstantStringSymbol("b"))
        val c = FOLConst(ConstantStringSymbol("c"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val gb = Function(ConstantStringSymbol("g"),b::Nil)
        val gc = Function(ConstantStringSymbol("g"),c::Nil)
        val t9 = Function(ConstantStringSymbol("f"), gx::y::Nil)
        val t10 = Function(ConstantStringSymbol("f"), y::gb::Nil)
   //     alg.printSubst(alg.unify(t9,t10).get)
        (alg.unify(t9,t10)) must beEqual (Some(Substitution(SingleSubstitution(y,gb) :: SingleSubstitution(x,b) :: Nil)))
    }

    "return the substitution {x->a,y->b} where a and b are constants, x and y are variables" in {
        val t1 = Function(ConstantStringSymbol("f"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t2 = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
     //   alg.printSubst(alg.removeRedundanceFromSubst(alg.unify(t1, t2).get))
        (alg.unify(t1, t2)) must beEqual (Some(Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("x")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("a")).asInstanceOf[LambdaExpression])::Nil):::Substitution( SingleSubstitution(FOLVar(VariableStringSymbol("y")).asInstanceOf[Var], FOLConst(ConstantStringSymbol("b")).asInstanceOf[LambdaExpression])::Nil)))
    }
    
    "applies the substitution {x->b} to the substitution {y->f(g(x),c),z->f(c,b)}" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val z = FOLVar(VariableStringSymbol("z"))
        val b = FOLConst(ConstantStringSymbol("b"))
        val c = FOLConst(ConstantStringSymbol("c"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val gb = Function(ConstantStringSymbol("g"),b::Nil)
        val f_gx_y = Function(ConstantStringSymbol("f"), gx::y::Nil)
        val f_gx_c = Function(ConstantStringSymbol("f"), gx::c::Nil)
        val f_gb_c = Function(ConstantStringSymbol("f"), gb::c::Nil)
        val f_c_b = Function(ConstantStringSymbol("f"), c::b::Nil)
        val f_y_gb = Function(ConstantStringSymbol("f"), y::gb::Nil)
        var s1 = Substitution(SingleSubstitution(y,f_gx_c) :: SingleSubstitution(z,f_c_b) :: Nil)
        var s2 = Substitution(SingleSubstitution(x,b) :: Nil)
        var s3 = Substitution(SingleSubstitution(y,f_gb_c) :: SingleSubstitution(z,f_c_b) :: Nil)      
        //alg.printSubst(alg.applySub(s1, s2))
        (alg.applySub(s1, s2)) must beEqual (s3)
      //  (0) must beEqual (0)
    }

    "return None when trying to unify the pair <f(x,y), f(y,g(x))>" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val f_x_y = Function(ConstantStringSymbol("f"), x::y::Nil)
        val f_y_gx = Function(ConstantStringSymbol("f"), y::gx::Nil)
 //       alg.printSubst(alg.unify(f_x_y, f_y_gx))
        (alg.unify(f_x_y, f_y_gx)) must beEqual (None)
      //  (0) must beEqual (0)
    }
  }*/
}
