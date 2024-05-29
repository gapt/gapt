/*
 * NaiveIncompleteMatchingAlgorithmTest.scala
 *
 */

package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.formula.Atom
import gapt.expr.subst.Substitution
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.util.syntacticMatching
import org.specs2.mutable._

class NaiveIncompleteMatchingAlgorithmTest extends Specification {
  "NaiveIncompleteMatchingAlgorithm " should {
    "match correctly the HOL expressions P(a,x) and P(a,f(b))" in {
      val P = Const("P", Ti ->: Ti ->: To)
      val a = Const("a", Ti)
      val b = Const("b", Ti)
      val Pa = App(P, a);
      val x = Var("x", Ti)
      val Pax = App(Pa, x)
      val f = Const("f", Ti ->: Ti)
      val fb = App(f, b)
      val Pafb = App(Pa, fb)
      val subst = syntacticMatching(Pax, Pafb)
      val subst1 = Substitution(x, fb)
      subst must beEqualTo(Some(subst1))
    }

    "match correctly the HOL expressions P(z,x) and P(f(b),f(b))" in {
      val P = Const("P", Ti ->: Ti ->: To)
      val b = Const("b", Ti)
      val x = Var("x", Ti)
      val z = Var("z", Ti)
      val Pz = App(P, z)

      val Pzx = App(Pz, x)
      val f = Const("f", Ti ->: Ti)
      val fb = App(f, b)
      val Pfb = App(P, fb)
      val Pfbfb = App(Pfb, fb)
      val subst = syntacticMatching(Pzx, Pfbfb)
      val subst1 = Substitution(Map((x, fb), (z, fb)))
      subst must beEqualTo(Some(subst1))
    }

    "NOT match correctly the HOL expressions P(z,x) and P(f(b),z)" in {
      val P = Const("P", Ti ->: Ti ->: To)
      val b = Const("b", Ti)
      val x = Var("x", Ti)
      val z = Var("z", Ti)
      val Pz = App(P, z)
      val Pzx = App(Pz, x)
      val f = Const("f", Ti ->: Ti)
      val fb = App(f, b)
      val Pfb = App(P, fb)
      val Pfbz = App(Pfb, z)
      val subst = syntacticMatching(Pzx, Pfbz)
      val subst1 = Substitution(Map((z, fb), (x, z)))
      subst must beEqualTo(Some(subst1))
    }

    "match correctly the HOL expression a < p(x) with itself" in {
      val lt = Const("<", Ti ->: Ti ->: To)
      val a = Const("a", Ti)
      val p = Const("p", Ti ->: Ti)
      val x = Var("x", Ti)
      val px = HOLFunction(p, x :: Nil)
      val at = Atom(lt, a :: px :: Nil)
      val subst = syntacticMatching(at, at)
      subst must beEqualTo(Some(Substitution(x -> x)))
    }

    "match correctly the HOL expression a < p(x) with another copy of itself" in {
      val lt = Const("<", Ti ->: Ti ->: To)
      val a = Const("a", Ti)
      val p = Const("p", Ti ->: Ti)
      val x = Var("x", Ti)
      val px = HOLFunction(p, x :: Nil)
      val at = Atom(lt, a :: px :: Nil)
      val at2 = Atom(lt, a :: px :: Nil) // Is this a copy?
      val subst = syntacticMatching(at, at2)
      subst must beEqualTo(Some(Substitution(x -> x)))
    }
  }
}
