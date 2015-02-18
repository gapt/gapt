/*
 * FirstOrderLogicTest.scala
 */

package at.logic.gapt.language.fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.language.hol

@RunWith(classOf[JUnitRunner])
class FirstOrderLogicTest extends SpecificationWithJUnit {
  "FirstOrderLogic" should {
    "construct correctly an atom formula P(x,f(y),c)" in {
      val List( p, x,y,f,c ) = List("P","x","y","f","c")
      val Pc = FOLLambdaConst(p, (Ti -> (Ti -> (Ti -> To))) )
      FOLAtom( p, FOLVar(x)::FOLFunction(f,FOLVar(y)::Nil)::FOLConst(c)::Nil ) must beLike {
        case FOLApp( FOLApp( FOLApp( Pc, FOLVar(x) ), FOLApp( fc, FOLVar(y) ) ), FOLConst(c) ) => ok
      }
    }
    "construct correctly an atom using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1::var2::const1::Nil
      val atom1 = FOLAtom("A", args)
      val var3 = FOLAtom("X3")
      val and1 = FOLAnd(atom1, var3)
      true
    }
    "construct correctly a forall using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1::var2::const1::Nil
      val atom1 = FOLAtom("A",args)
      val all1 = FOLAllVar(var1, atom1)
      true
    }

    "alpha equality as default provides that ∀x.∀x.P(x) is equal to ∀y.∀y.P(y)" in {
      val x = FOLVar("x")
      val y = FOLVar("y")
      val p = "P"
      val px = FOLAtom(p,List(x))
      val py = FOLAtom(p,List(y))
      val allall_px = FOLAllVar(x, FOLAllVar(x, px))
      val allall_py = FOLAllVar(y, FOLAllVar(y, py))

      allall_px must beEqualTo (allall_py)
    }
  }

  "First Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val ps = "P"
      val f = FOLAnd(FOLAtom(ps), FOLAtom(ps))

      f must beLike {
        case FOLAtom(_,_) => ko
        case FOLAllVar(_,_) => ko
        case FOLExVar(_,_) => ko
        case FOLOr(_,_) => ko
        case FOLImp(_,_) => ko
        case FOLAnd(_,_) => ok
        case _ => ko
      }
    }
    "match Equation with Atom" in {
      val a = FOLConst("a").asInstanceOf[FOLTerm]
      val b = FOLConst("b").asInstanceOf[FOLTerm]
      val eq = FOLEquation(a, b)

      eq must beLike {
        case FOLAtom(_,_) => ok
        case _ => ko
      }
    }
  }

  "First order formulas matching against higher order contructors" should {
    "work for propositional logical operators" in {
      val List(x,y) = List("x","y") map (FOLVar(_))
      val p = "P"
      val pab = FOLAtom(p, List(x,y))

      FOLAnd(pab,pab) match {
        case hol.HOLAnd(a,b) =>
          a mustEqual(pab)
          b mustEqual(pab)
        case _ => ko("FOL Conjunction did not match against HOL Conjunction!")
      }

      FOLOr(pab,pab) match {
        case hol.HOLOr(a,b) =>
          a mustEqual(pab)
          b mustEqual(pab)
        case _ => ko("FOL Disjunction did not match against HOL Conjunction!")
      }

      FOLNeg(pab) match {
        case hol.HOLNeg(a) =>
          a mustEqual(pab)
        case _ => ko("FOL Negation did not match against HOL Conjunction!")
      }
    }

    "work for quantifiers" in {
      val List(a,b) = List("a","b") map (FOLConst(_))
      val List(x,y) = List("x","y") map (FOLVar(_))
      val p = "P"
      val pab = FOLAtom(p, List(a,b))

      FOLAllVar(x,pab) match {
        case hol.HOLAllVar(v,f) =>
          v mustEqual(x)
          f mustEqual(pab)
        case _ => ko("FOL AllVar did not match against HOL Conjunction!")
      }

      FOLExVar(x,pab) match {
        case hol.HOLExVar(v,f) =>
          v mustEqual(x)
          f mustEqual(pab)
        case _ => ko("FOL ExVar did not match against HOL Conjunction!")
      }
    }

    "work well together with the hol layer" in {
      val a1 = FOLAtom("P",List(FOLConst("a")))
      val a2 = FOLAtom("Q",List(FOLVar("x")))
      val neg = hol.HOLNeg(a1)
      val conj = hol.HOLAnd(a1,a2)
      val or = hol.HOLOr(a1,a2)
      val imp = hol.HOLImp(a1,a2)
      val (t1,t2) = (FOLConst("a"), FOLVar("x"))
      val eq = hol.HOLEquation(t1,t2)
      val all = hol.HOLAllVar(t2, a2)
      val ex = hol.HOLExVar(t2, a2)
      neg match {
        case FOLNeg(b1) =>
          a1 must_== b1
        case _ => ko("HOL created negation did not match against fol conjunction!")
      }
      conj match {
        case FOLAnd(b1,b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created conjunction did not match against fol conjunction!")
      }
      or match {
        case FOLOr(b1,b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created disjunction did not match against fol conjunction!")
      }
      imp match {
        case FOLImp(b1,b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created implication did not match against fol conjunction!")
      }
      eq match {
        case FOLEquation(b1,b2) =>
          t1 must_== b1
          t2 must_== b2
        case _ => ko("HOL created equation did not match against fol conjunction!")
      }
      all match {
        case FOLAllVar(b1,b2) =>
          t2 must_== b1
          a2 must_== b2
        case _ => ko("HOL created universal quantification did not match against fol conjunction!")
      }
      ex match {
        case FOLExVar(b1,b2) =>
          t2 must_== b1
          a2 must_== b2
        case _ => ko("HOL created existential quantification did not match against fol conjunction!")
      }

    }

    "work well together with the hol layer" in {
      val a1 = FOLAtom("P",List(FOLConst("a")))
      val a2 = FOLAtom("Q",List(FOLVar("x")))
      val neg = FOLNeg(a1)
      val conj = FOLAnd(a1,a2)
      val or = FOLOr(a1,a2)
      val imp = FOLImp(a1,a2)
      val (t1,t2) = (FOLConst("a"), FOLVar("x"))
      val eq = FOLEquation(t1,t2)
      val all = FOLAllVar(t2, a2)
      val ex = FOLExVar(t2, a2)
      neg match {
        case hol.HOLNeg(b1) =>
          ok
        case _ => ko("HOL created negation did not match against fol conjunction!")
      }
      conj match {
        case hol.HOLAnd(b1,b2) =>
          ok
        case _ => ko("HOL created conjunction did not match against fol conjunction!")
      }
      or match {
        case hol.HOLOr(b1,b2) =>
          ok
        case _ => ko("HOL created disjunction did not match against fol conjunction!")
      }
      imp match {
        case hol.HOLImp(b1,b2) =>
          ok
        case _ => ko("HOL created implication did not match against fol conjunction!")
      }
      eq match {
        case hol.HOLEquation(b1,b2) =>
          ok
        case _ => ko("HOL created equation did not match against fol conjunction!")
      }
      all match {
        case hol.HOLAllVar(b1,b2) =>
          ok
        case _ => ko("HOL created universal quantification did not match against fol conjunction!")
      }
      ex match {
        case hol.HOLExVar(b1,b2) =>
          ok
        case _ => ko("HOL created existential quantification did not match against fol conjunction!")
      }
      ok
    }


  }

}
