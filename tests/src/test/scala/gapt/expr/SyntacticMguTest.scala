package gapt.expr

import gapt.expr.util.syntacticMGU
import org.specs2.mutable._

class SyntacticMguTest extends Specification {

  "not unify bound variables" in {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val f = FOLFunctionConst( "f", 2 )
    val g = FOLFunctionConst( "g", 1 )

    syntacticMGU(
      Abs( x, Abs( y, f( x, y ) ) ),
      Abs( x, Abs( y, f( y, x ) ) ) ) must beNone
    syntacticMGU(
      Abs( x, Abs( y, g( x ) ) ),
      Abs( x, Abs( y, y ) ) ) must beNone
  }

  "handle variables that are both bound and free" in {
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val f = Const( "f", Ti ->: ( Ti ->: Ti ) ->: Ti )
    val g = FOLFunctionConst( "g", 1 )
    val c = FOLConst( "c" )

    syntacticMGU(
      f( x, Abs( y, x ) ),
      f( g( y ), Abs( z, g( c ) ) ) ) must beSome
  }

  "FOL Unification" should {
    "P(x_1), P(x_2)" in {
      syntacticMGU( foa"P x_1", foa"P x_2" ) must_== Some(
        FOLSubstitution( fov"x_1" -> fot"x_2" ) )
    }
    "a, b" in { syntacticMGU( fot"a", fot"b" ) must beEmpty }
    "f(a), g(a)" in { syntacticMGU( fot"f a", fot"g a" ) must beEmpty }
    "empty substitution" in {
      "constants" in { syntacticMGU( fot"a", fot"a" ) must_== Some( FOLSubstitution() ) }
      "constants" in { syntacticMGU( fot"f a", fot"f a" ) must_== Some( FOLSubstitution() ) }
    }
    "x, a" in { syntacticMGU( fot"x", fot"a" ) must_== Some( FOLSubstitution( fov"x" -> fot"a" ) ) }
    "z, f(g(x,a),y,b)" in {
      syntacticMGU( fot"z", fot"f(g x a, y, b)" ) must_== Some( FOLSubstitution( fov"z" -> fot"f(g x a, y, b)" ) )
    }
    "a,f(g(x,a),y,b)" in { syntacticMGU( fot"a", fot"f(g x a, y, b)" ) must beEmpty }
    "x, f(g(x,a),y,b)" in { syntacticMGU( fot"x", fot"f(g(x,a),y,b)" ) must beEmpty }

    "f(g(c),y), f(y,g(b))" in { syntacticMGU( fot"f(g(c),y)", fot"f(y,g(b))" ) must beEmpty }
    "f(g(x),y), f(y,g(b))" in {
      syntacticMGU( fot"f(g(x),y)", fot"f(y,g(b))" ) must_== Some( FOLSubstitution( fov"y" -> fot"g b", fov"x" -> fot"b" ) )
    }

    "f(x,b), f(a,y)" in { syntacticMGU( fot"f x b", fot"f a y" ) must_== Some( FOLSubstitution( fov"x" -> fot"a", fov"y" -> fot"b" ) ) }

    "real-world example" in {
      val t1 = hof"""
        ¬ladr1 = ladr3(ladr2(#v(B: i), #v(A: i))) ∨
          ladr0 = ladr3(ladr2(ladr2(ladr0, ladr2(#v(B: i), #v(A: i))), #v(C: i)))
        """
      val t2 = hof"""
        ¬ladr1 = ladr3(ladr2('x_{3}', 'x_{2}')) ∨
          ladr0 = ladr3(ladr2(ladr2(ladr0, ladr2('x_{3}', 'x_{2}')), 'x_{4}'))
        """

      syntacticMGU( t1, t2 ) must_== Some( FOLSubstitution(
        fov"#v(B:i)" -> fot"'x_{3}'",
        fov"#v(A:i)" -> fot"'x_{2}'",
        fov"#v(C:i)" -> fot"'x_{4}'" ) )
    }

  }

  "f(x, x), f(a, b)" in { syntacticMGU( le"f x x", le"f a b" ) must beEmpty }

  "x x" in { syntacticMGU( le"x:i", le"x:?a" ) must beSome }

}
