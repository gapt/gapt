/*
 * hol2folTest.scala
 */

package gapt.expr.formula.fol

import gapt.expr._
import gapt.expr.formula
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.constants.ImpC
import gapt.expr.formula.hol.HOLFunction
import gapt.expr.subst.Substitution
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.expr.util
import gapt.expr.util.constants
import gapt.expr.util.subTerms
import gapt.utils.Counter
import org.specs2.mutable._

class hol2folTest extends Specification {
  "HOL terms" should {
    "be correctly reduced into FOL terms for" in {
      "Atom - A(x:(i->i), a:o->i)" in {
        implicit val d = new Hol2FolDefinitions
        val hol = hoa"A( #v(x: i>i), #c(a:o>i) )"
        val fol = foa"A( #v(x:i), #c(a:i) )"
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        implicit val d = new Hol2FolDefinitions
        val hol = le"f( #v(x:i>i), #c(a:o>i))"
        val fol = fot"f(x, a)"
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        implicit val d = new Hol2FolDefinitions
        val hol = hof"A( #v(x:i>i), #c(a:o>i) ) & B( #v(x:i>i), #c(b:o>i) )"
        val fol = fof"A( #v(x:i), #c(a:i) ) & B( #v(x:i), #c(b:i) )"
        reduceHolToFol( hol ) must beEqualTo( fol )
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" in {
        implicit val d = new Hol2FolDefinitions
        val holf = le"f(λ(x:i>i) A(x, a:o>i)):o>o"
        val folf = fot"f('q_{1}')"
        reduceHolToFol( holf ) must beEqualTo( folf )
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" in {
        implicit val d = new Hol2FolDefinitions
        val red = reduceHolToFol( le"f(λ(x:i>i) A(x, y:o>i)):o>o" )
        val fol = fot"f('q_{1}'(y))"
        red must beEqualTo( fol )
      }
      "Matching abstractions should reuse definition" in {
        implicit val d = new Hol2FolDefinitions
        reduceHolToFol( le"f(λ(x:i>i) A(x, y:o>i)):o>o" ) mustEqual fot"f('q_{1}'(y))"
        reduceHolToFol( le"g(λ(x:i>i) A(x, z:o>i)):o>o" ) mustEqual fot"g('q_{1}'(z))"
      }
      "Correctly convert from type o to i on the termlevel" in {
        implicit val d = new Hol2FolDefinitions
        val holAtom = hoa"P( #v(x:o) → #v(y:o) )"
        val folAtom = foa"P(#c(→: i>i>i) #v(x:i)  #v(y:i) )"
        reduceHolToFol( holAtom ) must beEqualTo( folAtom )
      }
    }
  }

  "Type replacement" should {
    "work for simple terms" in {
      val folTerm: FOLTerm = fot"f q_1 c"
      val holTerm = changeTypeIn( folTerm, Map[String, Ty]( ( "q_1", Ti ->: Ti ) ) )
      holTerm mustEqual le"(f : (i > i) > i > i) (q_1 : i > i) c"
    }
    "work for simple formulas" in {
      val folFormula: FOLFormula = fof"!x (P #v( q_1 : i) #c( q_1 : i ) )"
      val holFormula = changeTypeIn( folFormula, Map[String, Ty]( ( "q_1", Ti ->: Ti ) ) )
      holFormula mustEqual hof"!x ((P : (i > i) > (i > i) > o) #v( q_1 : i > i) #c( q_1 : i > i) )"
    }
  }

  "replacing abstractions" should {
    "replace outermost abstractions by constants" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"^x ^y ^z (x y z)"
      val r = replaceAbstractions( t )
      r must beAnInstanceOf[Const]
    }
    "types of defining constants should agree with defined abstraction" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"^(x:i) ^(y:i) ^(z:i) (#c(f:i>i>i>i) x y z)"
      val c @ Const( _, _, _ ) = replaceAbstractions( t )
      c.ty mustEqual ty"i > i > i >i"
    }
    "defining constant must be applied to free variables of defined abstraction" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"^(x:i>i>i) (x #v(a:i) #v(b:i))"
      val Apps( _: Const, a :: b :: Nil ) = replaceAbstractions( t )
      a mustEqual Var( "a", Ti )
      b mustEqual Var( "b", Ti )
    }
    "replace all outermost abstractions by constants" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"(^x x)(^x (f x))"
      val r = replaceAbstractions( t )
      subTerms( r ) foreach { case _: Abs => failure; case _ => }
      ok
    }
    "should introduce one constant per abstraction modulo uniformity" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"#c(f: (i>i)>(i>i)>i) (^x x) (^x x)"
      val Apps( _: Const, ( c1: Const ) :: ( c2: Const ) :: Nil ) = replaceAbstractions( t )
      c1 mustEqual c2
    }
    "definition must account for free variables" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"(^(x:i>i) x)(^x (#v(f:i>i) x))"
      replaceAbstractions( t )
      val Apps( _: Const, Nil ) = d.getDefinedExpression( le"^(x:i>i) x" )
      val Apps( _: Const, f :: Nil ) = d.getDefinedExpression( le"^x (#v(f:i>i) x)" )
      f mustEqual le"#v(f:i>i)"
    }
    "definition must match over free variables" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"(^x (#v(f:i>i) x))"
      replaceAbstractions( t )
      val Apps( _: Const, a :: Nil ) = d.getDefinedExpression( le"^x (#c(a:i>i) x)" )
      a mustEqual hoc"a:i>i"
    }
    "no unnecessary constants should be introduced" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"(^(x:i>i) x)(^x (#v(f:i>i) x))"
      val r @ App( r1 @ Apps( c1: Const, _ ), r2 @ Apps( c2: Const, _ ) ) = replaceAbstractions( t )
      d.toMap.keys mustEqual Set( r1, r2 )
      util.constants.nonLogical( r ) mustEqual Set( c1, c2 )
    }
    "replace non-uniform abstracts by different constants" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"#v(f:(i>i)>((i>i)>(i>i))>i) (^x x) (^x x)"
      val Apps( _, ( c1: Const ) :: ( c2: Const ) :: Nil ) = replaceAbstractions( t )
      c1 must_!= c2
    }
    "keep introducing new constants" in {
      implicit val d = new Hol2FolDefinitions
      val t1: Expr = le"^x x"
      val c1 @ Const( _, _, _ ) = replaceAbstractions( t1 )
      d.toMap.size mustEqual 1
      val t2: Expr = le"^(x:i>i) x"
      val c2 @ Const( _, _, _ ) = replaceAbstractions( t2 )
      d.toMap.size mustEqual 2
      c1 must_!= c2
    }
    "leave abstractions of quantifiers intact" in {
      val f: Formula = hof"!x x = x & ?y y = y"
      val r = replaceAbstractions( f )( new Hol2FolDefinitions() )
      r mustEqual f
    }
  }
  "undoing abstractions should" in {
    "restore restore original expression" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"#v(f:(i>i)>((i>i)>(i>i))>i) (^x x) (^x x)"
      val r = replaceAbstractions( t )
      undoReplaceAbstractions( r, d ) mustEqual t
    }
  }
  "reversing lifting of abstractions with free variables should" in {
    "restore original expression" in {
      implicit val d = new Hol2FolDefinitions
      val t: Expr = le"^x #v(a:i)"
      val r = replaceAbstractions( t )
      BetaReduction.normalize( undoReplaceAbstractions( r, d ) ) mustEqual t
    }
  }
  "definitions" should {
    "be equal if identical" in {
      val d = new Hol2FolDefinitions()
      d mustEqual d
    }
    "be equal if they differ only in the naming of free variables (empty case)" in {
      val d1 = new Hol2FolDefinitions()
      val d2 = new Hol2FolDefinitions()
      d1 mustEqual d2
    }
    "be equal if they differ only in the naming of free variables (nonempty case)" in {
      val d1 = new Hol2FolDefinitions()
      val d2 = new Hol2FolDefinitions()
      d1.getDefinedExpression( le"#v(a:i)" )
      d2.getDefinedExpression( le"#v(b:i)" )
      d1 mustEqual d2
    }
    "not be equal if definitions differ not only in free variables" in {
      val d1 = new Hol2FolDefinitions()
      val d2 = new Hol2FolDefinitions()
      d1.getDefinedExpression( le"#v(a:i)" )
      d2.getDefinedExpression( le"#c(b:i)" )
      d1 must_!== d2
    }
  }
}
