
package at.logic.algorithms.unification

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
//import at.logic.language.lambda.types._
//import at.logic.language.hol.logicSymbols._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

@RunWith(classOf[JUnitRunner])
class UnificationTest extends SpecificationWithJUnit {
  
  "FOL Unification" should {
    "unify the terms" in {
      "P(x_1), P(x_2)" in {
        val x1 = FOLVar("x_1")
        val x2 = FOLVar("x_2")
        val px1 = Atom("P", x1::Nil)
        val px2 = Atom("P", x2::Nil)
        (FOLUnificationAlgorithm.unify(px1,px2)) must_== 
          (List(Substitution(FOLVar("x_1"), FOLVar("x_2"))))

      }
    }
    "return Nil if terms are not unifiable" in
    {
      "- both are constants" in
      {
        val a = FOLConst("a")
        val b = FOLConst("b")
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Nil)
      }
      "- both are functions" in {
        val a = Function("f", FOLConst("a")::Nil)
        val b = Function("g", FOLConst("a")::Nil)
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Nil)
      }
    }
    "return Empty substitution if both terms are" in {
      "constants" in {
        val a = FOLConst("a")
        val b = FOLConst("a")
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Substitution(Nil)::Nil)
      }
      "functions" in {
        val a = Function("f", FOLConst("a")::Nil)
        val b = Function("f", FOLConst("a")::Nil)
        (FOLUnificationAlgorithm.unify(a,b)) must beEqualTo (Substitution(Nil)::Nil)
      }
    }
    "returns the substitution {x->a} where a is a constant, x is a variable" in {
        val x = FOLVar("x")
        val a = FOLConst("a")
        (FOLUnificationAlgorithm.unify(x, a)) must beEqualTo (Substitution( FOLVar("x"), FOLConst("a"))::Nil)
    }
    "return a unifier for the pair <z,f(g(x,a),y,b)>, where x,y,z are vars, a and b are consts" in {
        val z = FOLVar("z")
        val t5 = Function("g", FOLVar("x")::FOLConst("b")::Nil)
        val t6 = Function("f", t5::FOLConst("a")::FOLVar("y")::Nil)
        (FOLUnificationAlgorithm.unify(z, t6)) must beEqualTo (Substitution( FOLVar("z"), t6)::Nil)
    }
    "return Nil for the pair <a,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
        val a = FOLConst("a")
        val t7 = Function("g", FOLVar("x")::FOLConst("b")::Nil)
        val t8 = Function("f", t7::FOLConst("a")::FOLVar("y")::Nil)
        (FOLUnificationAlgorithm.unify(a, t8)) must beEqualTo (Nil)
    }
    "return Nil for the pair <x,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
        val x = FOLVar("x")
        val t7 = Function("g", FOLVar("x")::FOLConst("b")::Nil)
        val t8 = Function("f", t7::FOLConst("a")::FOLVar("y")::Nil)
        (FOLUnificationAlgorithm.unify(x, t8)) must beEqualTo (Nil)
    }

    "return Nil for the pair <f(g(c),y), f(y,g(b))> where x,y are vars, a,c are consts" in {
        val x = FOLVar("x")
        val y = FOLVar("y")
        val b = FOLConst("b")
        val c = FOLConst("c")
        val gx = Function("g",x::Nil)
        val gb = Function("g",b::Nil)
        val gc = Function("g",c::Nil)
        val f_gc_y = Function("f", gc::y::Nil)
        val t_y_gb = Function("f", y::gb::Nil)
       (FOLUnificationAlgorithm.unify(f_gc_y, t_y_gb)) must beEqualTo (Nil)
    }

    "return the unifier {y->g(b), x->b} for the pair <f(g(x),y), f(y,g(b))> where x,y are vars, a and b are consts" in {
        val x = FOLVar("x")
        val y = FOLVar("y")
        val b = FOLConst("b")
        val c = FOLConst("c")
        val gx = Function("g",x::Nil)
        val gb = Function("g",b::Nil)
        val gc = Function("g",c::Nil)
        val t9 = Function("f", gx::y::Nil)
        val t10 = Function("f", y::gb::Nil)
        (FOLUnificationAlgorithm.unify(t9,t10)) must beEqualTo (Substitution( (y,gb)::(x,b)::Nil )::Nil)
    }

    "return the substitution {x->a,y->b} where a and b are constants, x and y are variables" in {
        val t1 = Function("f", FOLVar("x")::FOLConst("b")::Nil)
        val t2 = Function("f", FOLConst("a")::FOLVar("y")::Nil)
        (FOLUnificationAlgorithm.unify(t1, t2)) must beEqualTo (Substitution( (FOLVar("x"), FOLConst("a") )::(FOLVar("y"), FOLConst("b"))::Nil)::Nil)
    }

    // the following test was automatically generated using the toCode function
    "unify two formulas from a real-world example" in {
      val t1 = Or(Neg(Atom(  "=" , FOLConst(  "ladr1"  )::Function(  "ladr3" , Function(  "ladr2" , FOLVar(  "B"  )::FOLVar(  "A"  )::Nil)::Nil)::Nil)), Atom(  "=" , FOLConst(  "ladr0"  )::Function(  "ladr3" , Function(  "ladr2" , Function(  "ladr2" , FOLConst(  "ladr0"  )::Function(  "ladr2" , FOLVar(  "B"  )::FOLVar(  "A"  )::Nil)::Nil)::FOLVar(  "C"  )::Nil)::Nil)::Nil))

      val t2 = Or(Neg(Atom(  "=" , FOLConst(  "ladr1"  )::Function(  "ladr3" , Function(  "ladr2" , FOLVar(  "x_{3}"  )::FOLVar(  "x_{2}"  )::Nil)::Nil)::Nil)), Atom(  "=" , FOLConst(  "ladr0"  )::Function(  "ladr3" , Function(  "ladr2" , Function(  "ladr2" , FOLConst(  "ladr0"  )::Function(  "ladr2" , FOLVar(  "x_{3}"  )::FOLVar(  "x_{2}"  )::Nil)::Nil)::FOLVar(  "x_{4}"  )::Nil)::Nil)::Nil))

      (FOLUnificationAlgorithm.unify(t1, t2)) must beEqualTo (Substitution( (FOLVar(  "B"  ), FOLVar(  "x_{3}"  ))::(FOLVar(  "A"  ), FOLVar(  "x_{2}"  ))
                                                                        ::(FOLVar(  "C"  ), FOLVar(  "x_{4}"  ))::Nil)::Nil)
    }

  }
}
