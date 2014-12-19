/*
 * FirstOrderLogicTest.scala
 */

package at.logic.language.fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.language.hol

@RunWith(classOf[JUnitRunner])
class FirstOrderLogicTest extends SpecificationWithJUnit {
  "FirstOrderLogic" should {
    "construct correctly an atom formula P(x,f(y),c)" in {
      val List( p, x,y,f,c ) = List("P","x","y","f","c")
      val Pc = FOLLambdaConst(p, (Ti -> (Ti -> (Ti -> To))) )
      Atom( p, FOLVar(x)::Function(f,FOLVar(y)::Nil)::FOLConst(c)::Nil ) must beLike {
        case FOLApp( FOLApp( FOLApp( Pc, FOLVar(x) ), FOLApp( fc, FOLVar(y) ) ), FOLConst(c) ) => ok
      }
    }
    "construct correctly an atom using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1::var2::const1::Nil
      val atom1 = Atom("A", args)
      val var3 = Atom("X3")
      val and1 = And(atom1, var3)
      true
    }
    "construct correctly a forall using the factory" in {
      val var1 = FOLVar("x1")
      val const1 = FOLConst("c1")
      val var2 = FOLVar("x2")
      val args = var1::var2::const1::Nil
      val atom1 = Atom("A",args)
      val all1 = AllVar(var1, atom1)
      true
    }

    "alpha equality as default provides that ∀x.∀x.P(x) is equal to ∀y.∀y.P(y)" in {
      val x = FOLVar("x")
      val y = FOLVar("y")
      val p = "P"
      val px = Atom(p,List(x))
      val py = Atom(p,List(y))
      val allall_px = AllVar(x, AllVar(x, px))
      val allall_py = AllVar(y, AllVar(y, py))

      allall_px must beEqualTo (allall_py)
    }
  }

  "First Order Formula matching" should {
    "not allow P and P match as an Atom " in {
      val ps = "P"
      val f = And(Atom(ps), Atom(ps))

      f must beLike {
        case Atom(_,_) => ko
        case AllVar(_,_) => ko
        case ExVar(_,_) => ko
        case Or(_,_) => ko
        case Imp(_,_) => ko
        case And(_,_) => ok
        case _ => ko
      }
    }
    "match Equation with Atom" in {
      val a = FOLConst("a").asInstanceOf[FOLTerm]
      val b = FOLConst("b").asInstanceOf[FOLTerm]
      val eq = Equation(a, b)

      eq must beLike {
        case Atom(_,_) => ok
        case _ => ko
      }
    }
  }

  "First order formulas matching against higher order contructors" should {
    "work for propositional logical operators" in {
      val List(x,y) = List("x","y") map (FOLVar(_))
      val p = "P"
      val pab = Atom(p, List(x,y))

      And(pab,pab) match {
        case hol.And(a,b) =>
          a mustEqual(pab)
          b mustEqual(pab)
        case _ => ko("FOL Conjunction did not match against HOL Conjunction!")
      }

      Or(pab,pab) match {
        case hol.Or(a,b) =>
          a mustEqual(pab)
          b mustEqual(pab)
        case _ => ko("FOL Disjunction did not match against HOL Conjunction!")
      }

      Neg(pab) match {
        case hol.Neg(a) =>
          a mustEqual(pab)
        case _ => ko("FOL Negation did not match against HOL Conjunction!")
      }
    }

    "work for quantifiers" in {
      val List(a,b) = List("a","b") map (FOLConst(_))
      val List(x,y) = List("x","y") map (FOLVar(_))
      val p = "P"
      val pab = Atom(p, List(a,b))

      AllVar(x,pab) match {
        case hol.AllVar(v,f) =>
          v mustEqual(x)
          f mustEqual(pab)
        case _ => ko("FOL AllVar did not match against HOL Conjunction!")
      }

      ExVar(x,pab) match {
        case hol.ExVar(v,f) =>
          v mustEqual(x)
          f mustEqual(pab)
        case _ => ko("FOL ExVar did not match against HOL Conjunction!")
      }
    }

    "work well together with the hol layer" in {
      val a1 = Atom("P",List(FOLConst("a")))
      val a2 = Atom("Q",List(FOLVar("x")))
      val neg = hol.Neg(a1)
      val conj = hol.And(a1,a2)
      val or = hol.Or(a1,a2)
      val imp = hol.Imp(a1,a2)
      val (t1,t2) = (FOLConst("a"), FOLVar("x"))
      val eq = hol.Equation(t1,t2)
      val all = hol.AllVar(t2, a2)
      val ex = hol.ExVar(t2, a2)
      neg match {
        case Neg(b1) =>
          a1 must_== b1
        case _ => ko("HOL created negation did not match against fol conjunction!")
      }
      conj match {
        case And(b1,b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created conjunction did not match against fol conjunction!")
      }
      or match {
        case Or(b1,b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created disjunction did not match against fol conjunction!")
      }
      imp match {
        case Imp(b1,b2) =>
          a1 must_== b1
          a2 must_== b2
        case _ => ko("HOL created implication did not match against fol conjunction!")
      }
      eq match {
        case Equation(b1,b2) =>
          t1 must_== b1
          t2 must_== b2
        case _ => ko("HOL created equation did not match against fol conjunction!")
      }
      all match {
        case AllVar(b1,b2) =>
          t2 must_== b1
          a2 must_== b2
        case _ => ko("HOL created universal quantification did not match against fol conjunction!")
      }
      ex match {
        case ExVar(b1,b2) =>
          t2 must_== b1
          a2 must_== b2
        case _ => ko("HOL created existential quantification did not match against fol conjunction!")
      }

    }

    "work well together with the hol layer" in {
      val a1 = Atom("P",List(FOLConst("a")))
      val a2 = Atom("Q",List(FOLVar("x")))
      val neg = Neg(a1)
      val conj = And(a1,a2)
      val or = Or(a1,a2)
      val imp = Imp(a1,a2)
      val (t1,t2) = (FOLConst("a"), FOLVar("x"))
      val eq = Equation(t1,t2)
      val all = AllVar(t2, a2)
      val ex = ExVar(t2, a2)
      neg match {
        case hol.Neg(b1) =>
          ok
        case _ => ko("HOL created negation did not match against fol conjunction!")
      }
      conj match {
        case hol.And(b1,b2) =>
          ok
        case _ => ko("HOL created conjunction did not match against fol conjunction!")
      }
      or match {
        case hol.Or(b1,b2) =>
          ok
        case _ => ko("HOL created disjunction did not match against fol conjunction!")
      }
      imp match {
        case hol.Imp(b1,b2) =>
          ok
        case _ => ko("HOL created implication did not match against fol conjunction!")
      }
      eq match {
        case hol.Equation(b1,b2) =>
          ok
        case _ => ko("HOL created equation did not match against fol conjunction!")
      }
      all match {
        case hol.AllVar(b1,b2) =>
          ok
        case _ => ko("HOL created universal quantification did not match against fol conjunction!")
      }
      ex match {
        case hol.ExVar(b1,b2) =>
          ok
        case _ => ko("HOL created existential quantification did not match against fol conjunction!")
      }
      ok
    }


  }

}
