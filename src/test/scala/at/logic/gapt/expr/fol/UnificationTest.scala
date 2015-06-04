
package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import org.specs2.mutable._

class UnificationTest extends Specification {

  "FOL Unification" should {
    "unify the terms" in {
      "P(x_1), P(x_2)" in {
        val x1 = FOLVar( "x_1" )
        val x2 = FOLVar( "x_2" )
        val px1 = FOLAtom( "P", x1 :: Nil )
        val px2 = FOLAtom( "P", x2 :: Nil )
        ( FOLUnificationAlgorithm.unify( px1, px2 ) ) must_==
          ( List( FOLSubstitution( FOLVar( "x_1" ), FOLVar( "x_2" ) ) ) )

      }
    }
    "return Nil if terms are not unifiable" in
      {
        "- both are constants" in
          {
            val a = FOLConst( "a" )
            val b = FOLConst( "b" )
            ( FOLUnificationAlgorithm.unify( a, b ) ) must beEqualTo( Nil )
          }
        "- both are functions" in {
          val a = FOLFunction( "f", FOLConst( "a" ) :: Nil )
          val b = FOLFunction( "g", FOLConst( "a" ) :: Nil )
          ( FOLUnificationAlgorithm.unify( a, b ) ) must beEqualTo( Nil )
        }
      }
    "return Empty substitution if both terms are" in {
      "constants" in {
        val a = FOLConst( "a" )
        val b = FOLConst( "a" )
        ( FOLUnificationAlgorithm.unify( a, b ) ) must beEqualTo( FOLSubstitution( Nil ) :: Nil )
      }
      "functions" in {
        val a = FOLFunction( "f", FOLConst( "a" ) :: Nil )
        val b = FOLFunction( "f", FOLConst( "a" ) :: Nil )
        ( FOLUnificationAlgorithm.unify( a, b ) ) must beEqualTo( FOLSubstitution( Nil ) :: Nil )
      }
    }
    "returns the substitution {x->a} where a is a constant, x is a variable" in {
      val x = FOLVar( "x" )
      val a = FOLConst( "a" )
      ( FOLUnificationAlgorithm.unify( x, a ) ) must beEqualTo( FOLSubstitution( FOLVar( "x" ), FOLConst( "a" ) ) :: Nil )
    }
    "return a unifier for the pair <z,f(g(x,a),y,b)>, where x,y,z are vars, a and b are consts" in {
      val z = FOLVar( "z" )
      val t5 = FOLFunction( "g", FOLVar( "x" ) :: FOLConst( "b" ) :: Nil )
      val t6 = FOLFunction( "f", t5 :: FOLConst( "a" ) :: FOLVar( "y" ) :: Nil )
      ( FOLUnificationAlgorithm.unify( z, t6 ) ) must beEqualTo( FOLSubstitution( FOLVar( "z" ), t6 ) :: Nil )
    }
    "return Nil for the pair <a,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
      val a = FOLConst( "a" )
      val t7 = FOLFunction( "g", FOLVar( "x" ) :: FOLConst( "b" ) :: Nil )
      val t8 = FOLFunction( "f", t7 :: FOLConst( "a" ) :: FOLVar( "y" ) :: Nil )
      ( FOLUnificationAlgorithm.unify( a, t8 ) ) must beEqualTo( Nil )
    }
    "return Nil for the pair <x,f(g(x,a),y,b)>, where x,y are vars, a and b are consts" in {
      val x = FOLVar( "x" )
      val t7 = FOLFunction( "g", FOLVar( "x" ) :: FOLConst( "b" ) :: Nil )
      val t8 = FOLFunction( "f", t7 :: FOLConst( "a" ) :: FOLVar( "y" ) :: Nil )
      ( FOLUnificationAlgorithm.unify( x, t8 ) ) must beEqualTo( Nil )
    }

    "return Nil for the pair <f(g(c),y), f(y,g(b))> where x,y are vars, a,c are consts" in {
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )
      val b = FOLConst( "b" )
      val c = FOLConst( "c" )
      val gx = FOLFunction( "g", x :: Nil )
      val gb = FOLFunction( "g", b :: Nil )
      val gc = FOLFunction( "g", c :: Nil )
      val f_gc_y = FOLFunction( "f", gc :: y :: Nil )
      val t_y_gb = FOLFunction( "f", y :: gb :: Nil )
      ( FOLUnificationAlgorithm.unify( f_gc_y, t_y_gb ) ) must beEqualTo( Nil )
    }

    "return the unifier {y->g(b), x->b} for the pair <f(g(x),y), f(y,g(b))> where x,y are vars, a and b are consts" in {
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )
      val b = FOLConst( "b" )
      val c = FOLConst( "c" )
      val gx = FOLFunction( "g", x :: Nil )
      val gb = FOLFunction( "g", b :: Nil )
      val gc = FOLFunction( "g", c :: Nil )
      val t9 = FOLFunction( "f", gx :: y :: Nil )
      val t10 = FOLFunction( "f", y :: gb :: Nil )
      ( FOLUnificationAlgorithm.unify( t9, t10 ) ) must beEqualTo( FOLSubstitution( ( y, gb ) :: ( x, b ) :: Nil ) :: Nil )
    }

    "return the substitution {x->a,y->b} where a and b are constants, x and y are variables" in {
      val t1 = FOLFunction( "f", FOLVar( "x" ) :: FOLConst( "b" ) :: Nil )
      val t2 = FOLFunction( "f", FOLConst( "a" ) :: FOLVar( "y" ) :: Nil )
      ( FOLUnificationAlgorithm.unify( t1, t2 ) ) must beEqualTo( FOLSubstitution( ( FOLVar( "x" ), FOLConst( "a" ) ) :: ( FOLVar( "y" ), FOLConst( "b" ) ) :: Nil ) :: Nil )
    }

    // the following test was automatically generated using the toCode function
    "unify two formulas from a real-world example" in {
      val t1 = Or( Neg( FOLAtom( "=", FOLConst( "ladr1" ) :: FOLFunction( "ladr3", FOLFunction( "ladr2", FOLVar( "B" ) :: FOLVar( "A" ) :: Nil ) :: Nil ) :: Nil ) ), FOLAtom( "=", FOLConst( "ladr0" ) :: FOLFunction( "ladr3", FOLFunction( "ladr2", FOLFunction( "ladr2", FOLConst( "ladr0" ) :: FOLFunction( "ladr2", FOLVar( "B" ) :: FOLVar( "A" ) :: Nil ) :: Nil ) :: FOLVar( "C" ) :: Nil ) :: Nil ) :: Nil ) )

      val t2 = Or( Neg( FOLAtom( "=", FOLConst( "ladr1" ) :: FOLFunction( "ladr3", FOLFunction( "ladr2", FOLVar( "x_{3}" ) :: FOLVar( "x_{2}" ) :: Nil ) :: Nil ) :: Nil ) ), FOLAtom( "=", FOLConst( "ladr0" ) :: FOLFunction( "ladr3", FOLFunction( "ladr2", FOLFunction( "ladr2", FOLConst( "ladr0" ) :: FOLFunction( "ladr2", FOLVar( "x_{3}" ) :: FOLVar( "x_{2}" ) :: Nil ) :: Nil ) :: FOLVar( "x_{4}" ) :: Nil ) :: Nil ) :: Nil ) )

      ( FOLUnificationAlgorithm.unify( t1, t2 ) ) must beEqualTo( FOLSubstitution( ( FOLVar( "B" ), FOLVar( "x_{3}" ) ) :: ( FOLVar( "A" ), FOLVar( "x_{2}" ) )
        :: ( FOLVar( "C" ), FOLVar( "x_{4}" ) ) :: Nil ) :: Nil )
    }

  }
}
