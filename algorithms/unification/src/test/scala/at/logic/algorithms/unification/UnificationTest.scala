/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package at.logic.algorithms.unification

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Definitions._
//import at.logic.language.hol._
import at.logic.language.lambda.substitutions.Substitution
//import at.logic.language.hol.propositions._
//import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.language.simple._
import at.logic.parsing.readers.StringReader
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

@RunWith(classOf[JUnitRunner])
class UnificationTest extends SpecificationWithJUnit {
  private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser
  
  "FOL Unification" should {
    "unify the terms" in {
      "P(x_1), P(x_2)" in {
        val px1 = new MyParser("P(x_1)").getTerm.asInstanceOf[FOLExpression]
        val px2 = new MyParser("P(x_2)").getTerm.asInstanceOf[FOLExpression]
        (FOLUnificationAlgorithm.unify(px1,px2)) must_== 
          (List(Substitution(FOLVar(VariableStringSymbol("x_1")), FOLVar(VariableStringSymbol("x_2")))))

      }
    }
    "return Nil if terms are not unifiable" in
    {
      "- both are constants" in
      {
        val a = FOLConst(ConstantStringSymbol("a"))
        val b = FOLConst(ConstantStringSymbol("b"))
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Nil)
      }
      "- both are functions" in {
        val a = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::Nil)
        val b = Function(ConstantStringSymbol("g"), FOLConst(ConstantStringSymbol("a"))::Nil)
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Nil)
      }
    }
    "return Empty substitution if both terms are" in {
      "constants" in {
        val a = FOLConst(ConstantStringSymbol("a"))
        val b = FOLConst(ConstantStringSymbol("a"))
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Substitution(Nil)::Nil)
      }
      "functions" in {
        val a = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::Nil)
        val b = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::Nil)
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Substitution(Nil)::Nil)
      }
    }
    "returns the substitution {x->a} where a is a constant, x is a variable" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val a = FOLConst(ConstantStringSymbol("a"))
        (FOLUnificationAlgorithm.unify(x, a)) must beEqualTo (Substitution( FOLVar(VariableStringSymbol("x")), FOLConst(ConstantStringSymbol("a")))::Nil)
    }
    /*
    "returns a list of all variables (i.e. x::y::Nil) in the term  f(g(x,a),y,b), where a and b are constants " in {
        val t3 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t4 = Function(ConstantStringSymbol("f"), t3::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (FOLUnificationAlgorithm.getVars(t4)) must beEqualTo (FOLVar(VariableStringSymbol("x"))::FOLVar(VariableStringSymbol("y"))::Nil)
    } */
    "return a unifier for the pair <z,f(g(x,a),y,b)>, where x,y,z are vars, a and b are consts" in {
        val z = FOLVar(VariableStringSymbol("z"))
        val t5 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t6 = Function(ConstantStringSymbol("f"), t5::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (FOLUnificationAlgorithm.unify(z, t6)) must beEqualTo (Substitution( FOLVar(VariableStringSymbol("z")), t6)::Nil)
    }
    "return Nil for the pair <a,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
        val a = FOLConst(ConstantStringSymbol("a"))
        val t7 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t8 = Function(ConstantStringSymbol("f"), t7::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (FOLUnificationAlgorithm.unify(a, t8)) must beEqualTo (Nil)
    }
    "return Nil for the pair <x,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val t7 = Function(ConstantStringSymbol("g"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t8 = Function(ConstantStringSymbol("f"), t7::FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (FOLUnificationAlgorithm.unify(x, t8)) must beEqualTo (Nil)
    }

    "return Nil for the pair <f(g(c),y), f(y,g(b))> where x,y are vars, a,c are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val b = FOLConst(ConstantStringSymbol("b"))
        val c = FOLConst(ConstantStringSymbol("c"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val gb = Function(ConstantStringSymbol("g"),b::Nil)
        val gc = Function(ConstantStringSymbol("g"),c::Nil)
        val f_gc_y = Function(ConstantStringSymbol("f"), gc::y::Nil)
        val t_y_gb = Function(ConstantStringSymbol("f"), y::gb::Nil)
       (FOLUnificationAlgorithm.unify(f_gc_y, t_y_gb)) must beEqualTo (Nil)
    }

    "return the unifier {y->g(b), x->b} for the pair <f(g(x),y), f(y,g(b))> where x,y are vars, a and b are consts" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val b = FOLConst(ConstantStringSymbol("b"))
        val c = FOLConst(ConstantStringSymbol("c"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val gb = Function(ConstantStringSymbol("g"),b::Nil)
        val gc = Function(ConstantStringSymbol("g"),c::Nil)
        val t9 = Function(ConstantStringSymbol("f"), gx::y::Nil)
        val t10 = Function(ConstantStringSymbol("f"), y::gb::Nil)
        (FOLUnificationAlgorithm.unify(t9,t10)) must beEqualTo (Substitution( (y,gb)::(x,b)::Nil )::Nil)
    }

    "return the substitution {x->a,y->b} where a and b are constants, x and y are variables" in {
        val t1 = Function(ConstantStringSymbol("f"), FOLVar(VariableStringSymbol("x"))::FOLConst(ConstantStringSymbol("b"))::Nil)
        val t2 = Function(ConstantStringSymbol("f"), FOLConst(ConstantStringSymbol("a"))::FOLVar(VariableStringSymbol("y"))::Nil)
        (FOLUnificationAlgorithm.unify(t1, t2)) must beEqualTo (Substitution( (FOLVar(VariableStringSymbol("x")), FOLConst(ConstantStringSymbol("a")) )::(FOLVar(VariableStringSymbol("y")), FOLConst(ConstantStringSymbol("b")))::Nil)::Nil)
    }

    // the following test was automatically generated using the toCode function
    "unify two formulas from a real-world example" in {
      val t1 = Or(Neg(Atom( ConstantStringSymbol( "=" ), FOLConst( ConstantStringSymbol( "ladr1" ) )::Function( ConstantStringSymbol( "ladr3" ), Function( ConstantStringSymbol( "ladr2" ), FOLVar( VariableStringSymbol( "B" ) )::FOLVar( VariableStringSymbol( "A" ) )::Nil)::Nil)::Nil)), Atom( ConstantStringSymbol( "=" ), FOLConst( ConstantStringSymbol( "ladr0" ) )::Function( ConstantStringSymbol( "ladr3" ), Function( ConstantStringSymbol( "ladr2" ), Function( ConstantStringSymbol( "ladr2" ), FOLConst( ConstantStringSymbol( "ladr0" ) )::Function( ConstantStringSymbol( "ladr2" ), FOLVar( VariableStringSymbol( "B" ) )::FOLVar( VariableStringSymbol( "A" ) )::Nil)::Nil)::FOLVar( VariableStringSymbol( "C" ) )::Nil)::Nil)::Nil))

      val t2 = Or(Neg(Atom( ConstantStringSymbol( "=" ), FOLConst( ConstantStringSymbol( "ladr1" ) )::Function( ConstantStringSymbol( "ladr3" ), Function( ConstantStringSymbol( "ladr2" ), FOLVar( VariableStringSymbol( "x_{3}" ) )::FOLVar( VariableStringSymbol( "x_{2}" ) )::Nil)::Nil)::Nil)), Atom( ConstantStringSymbol( "=" ), FOLConst( ConstantStringSymbol( "ladr0" ) )::Function( ConstantStringSymbol( "ladr3" ), Function( ConstantStringSymbol( "ladr2" ), Function( ConstantStringSymbol( "ladr2" ), FOLConst( ConstantStringSymbol( "ladr0" ) )::Function( ConstantStringSymbol( "ladr2" ), FOLVar( VariableStringSymbol( "x_{3}" ) )::FOLVar( VariableStringSymbol( "x_{2}" ) )::Nil)::Nil)::FOLVar( VariableStringSymbol( "x_{4}" ) )::Nil)::Nil)::Nil))

      (FOLUnificationAlgorithm.unify(t1, t2)) must beEqualTo (Substitution( (FOLVar( VariableStringSymbol( "B" ) ), FOLVar( VariableStringSymbol( "x_{3}" ) ))::(FOLVar( VariableStringSymbol( "A" ) ), FOLVar( VariableStringSymbol( "x_{2}" ) ))
                                                                        ::(FOLVar( VariableStringSymbol( "C" ) ), FOLVar( VariableStringSymbol( "x_{4}" ) ))::Nil)::Nil)
    }

  }
  /*
  val FOLUnificationAlgorithm = new FOLUnification {}
  "Unification" should {        
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
        //FOLUnificationAlgorithm.printSubst(FOLUnificationAlgorithm.applySub(s1, s2))
        (FOLUnificationAlgorithm.applySub(s1, s2)) must beEqualTo (s3)
      //  (0) must beEqualTo (0)
    }

    "return None when trying to unify the pair <f(x,y), f(y,g(x))>" in {
        val x = FOLVar(VariableStringSymbol("x"))
        val y = FOLVar(VariableStringSymbol("y"))
        val gx = Function(ConstantStringSymbol("g"),x::Nil)
        val f_x_y = Function(ConstantStringSymbol("f"), x::y::Nil)
        val f_y_gx = Function(ConstantStringSymbol("f"), y::gx::Nil)
 //       FOLUnificationAlgorithm.printSubst(FOLUnificationAlgorithm.unify(f_x_y, f_y_gx))
        (FOLUnificationAlgorithm.unify(f_x_y, f_y_gx)) must beEqualTo (None)
      //  (0) must beEqualTo (0)
    }
  }*/
}
