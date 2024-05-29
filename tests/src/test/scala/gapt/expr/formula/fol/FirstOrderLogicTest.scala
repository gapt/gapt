/*
 * FirstOrderLogicTest.scala
 */

package gapt.expr.formula.fol

import org.specs2.mutable._
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.ty.Ti
import gapt.expr.ty.To

class FirstOrderLogicTest extends Specification {
  "FirstOrderLogic" should {
    "construct correctly an atom formula P(x,f(y),c)" in {
      val List(p, x, y, f, c) = List("P", "x", "y", "f", "c")
      val Pc = Const(p, Ti ->: Ti ->: Ti ->: To)
      FOLAtom(p, FOLVar(x) :: FOLFunction(f, FOLVar(y) :: Nil) :: FOLConst(c) :: Nil) must beLike {
        case App(App(App(Pc, FOLVar(x)), App(fc, FOLVar(y))), FOLConst(c)) => ok
      }
    }
    "construct correctly an atom using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1 :: var2 :: const1 :: Nil
      val atom1 = FOLAtom("A", args)
      val var3 = FOLAtom("X3")
      val and1 = And(atom1, var3)
      true
    }
    "construct correctly a forall using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1 :: var2 :: const1 :: Nil
      val atom1 = FOLAtom("A", args)
      val all1 = All(var1, atom1)
      true
    }

    "alpha equality as default provides that ∀x.∀x.P(x) is equal to ∀y.∀y.P(y)" in {
      val x = FOLVar("x")
      val y = FOLVar("y")
      val p = "P"
      val px = FOLAtom(p, List(x))
      val py = FOLAtom(p, List(y))
      val allall_px = All(x, All(x, px))
      val allall_py = All(y, All(y, py))

      allall_px must beEqualTo(allall_py)
    }
  }

  "First Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val ps = "P"
      val f = And(FOLAtom(ps), FOLAtom(ps))

      f must beLike {
        case FOLAtom(_, _) => ko
        case All(_, _)     => ko
        case Ex(_, _)      => ko
        case Or(_, _)      => ko
        case Imp(_, _)     => ko
        case And(_, _)     => ok
        case _             => ko
      }
    }
    "match Equation with Atom" in {
      val a = FOLConst("a").asInstanceOf[FOLTerm]
      val b = FOLConst("b").asInstanceOf[FOLTerm]
      val eq = Eq(a, b)

      eq must beLike {
        case FOLAtom(_, _) => ok
        case _             => ko
      }
    }
  }

  "First order formulas matching against higher order contructors" should {
    "work for propositional logical operators" in {
      val List(x, y) = List("x", "y") map (FOLVar(_))
      val p = "P"
      val pab = FOLAtom(p, List(x, y))

      And(pab, pab) match {
        case And(a, b) =>
          a mustEqual (pab)
          b mustEqual (pab)
        case _ => ko("FOL Conjunction did not match against HOL Conjunction!")
      }

      Or(pab, pab) match {
        case Or(a, b) =>
          a mustEqual (pab)
          b mustEqual (pab)
        case _ => ko("FOL Disjunction did not match against HOL Conjunction!")
      }

      Neg(pab) match {
        case Neg(a) =>
          a mustEqual (pab)
        case _ => ko("FOL Negation did not match against HOL Conjunction!")
      }
    }

    "work for quantifiers" in {
      val List(a, b) = List("a", "b") map (FOLConst(_))
      val List(x, y) = List("x", "y") map (FOLVar(_))
      val p = "P"
      val pab = FOLAtom(p, List(a, b))

      All(x, pab) match {
        case All(v, f) =>
          v mustEqual (x)
          f mustEqual (pab)
        case _ => ko("FOL All did not match against HOL Conjunction!")
      }

      Ex(x, pab) match {
        case Ex(v, f) =>
          v mustEqual (x)
          f mustEqual (pab)
        case _ => ko("FOL Ex did not match against HOL Conjunction!")
      }
    }

    "work well together with the hol layer" in {
      val a1 = FOLAtom("P", List(FOLConst("a")))
      val a2 = FOLAtom("Q", List(FOLVar("x")))
      val neg = Neg(a1)
      val conj = And(a1, a2)
      val or = Or(a1, a2)
      val imp = Imp(a1, a2)
      val (t1, t2) = (FOLConst("a"), FOLVar("x"))
      val eq = Eq(t1, t2)
      val all = All(t2, a2)
      val ex = Ex(t2, a2)
      neg match {
        case Neg(b1) =>
          a1 must_== b1
        case _ => ko("HOL created negation did not match against fol conjunction!")
      }
      conj match {
        case And(b1, b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created conjunction did not match against fol conjunction!")
      }
      or match {
        case Or(b1, b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created disjunction did not match against fol conjunction!")
      }
      imp match {
        case Imp(b1, b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created implication did not match against fol conjunction!")
      }
      eq match {
        case Eq(b1, b2) =>
          t1 must_== b1
          t2 must_== b2
        case _ => ko("HOL created equation did not match against fol conjunction!")
      }
      all match {
        case All(b1, b2) =>
          t2 must_== b1
          a2 must_== b2
        case _ => ko("HOL created universal quantification did not match against fol conjunction!")
      }
      ex match {
        case Ex(b1, b2) =>
          t2 must_== b1
          a2 must_== b2
        case _ => ko("HOL created existential quantification did not match against fol conjunction!")
      }

    }

    "work well together with the hol layer" in {
      val a1 = FOLAtom("P", List(FOLConst("a")))
      val a2 = FOLAtom("Q", List(FOLVar("x")))
      val neg = Neg(a1)
      val conj = And(a1, a2)
      val or = Or(a1, a2)
      val imp = Imp(a1, a2)
      val (t1, t2) = (FOLConst("a"), FOLVar("x"))
      val eq = Eq(t1, t2)
      val all = All(t2, a2)
      val ex = Ex(t2, a2)
      neg match {
        case Neg(b1) =>
          ok
        case _ => ko("HOL created negation did not match against fol conjunction!")
      }
      conj match {
        case And(b1, b2) =>
          ok
        case _ => ko("HOL created conjunction did not match against fol conjunction!")
      }
      or match {
        case Or(b1, b2) =>
          ok
        case _ => ko("HOL created disjunction did not match against fol conjunction!")
      }
      imp match {
        case Imp(b1, b2) =>
          ok
        case _ => ko("HOL created implication did not match against fol conjunction!")
      }
      eq match {
        case Eq(b1, b2) =>
          ok
        case _ => ko("HOL created equation did not match against fol conjunction!")
      }
      all match {
        case All(b1, b2) =>
          ok
        case _ => ko("HOL created universal quantification did not match against fol conjunction!")
      }
      ex match {
        case Ex(b1, b2) =>
          ok
        case _ => ko("HOL created existential quantification did not match against fol conjunction!")
      }
      ok
    }
  }

  "FOLSubTerms" should {
    val a = FOLConst("a")
    val b = FOLConst("b")
    val ga = FOLFunction("g", a)
    val fgab = FOLFunction("f", ga, b)

    "work correctly on a FOLTerm" in {
      flatSubterms(fgab) must beEqualTo(Set(a, b, ga, fgab))
    }

    "work correctly on a List[FOLTerm]" in {
      flatSubterms(fgab :: ga :: Nil) must beEqualTo(Set(a, b, ga, fgab))
    }
  }
}
