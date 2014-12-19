/*
* LKTest.scala
*
*/

package at.logic.calculi.lk

import at.logic.language.lambda.Substitution
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._
import base._
import at.logic.language.fol.{Atom => FOLAtom, AllVar => FOLAllVar, ExVar => FOLExVar, FOLFormula, FOLConst, FOLVar}

/**
* The following properties of each rule are tested:
* 1) The right principal formula is created
* 2) The principal formula is managed correctly
* 3) The Auxiliaries formulas are managed in the correct way
* 4) The context is unchanged with regard to multiset equality
* 5) The formula occurrences are different from the upper sequents occurrences
*
* Still missing for each rule:
* 1) To check that all exceptions are thrown when needed
*/
@RunWith(classOf[JUnitRunner])
class LKTest extends SpecificationWithJUnit {

  val c1 = HOLVar("a", Ti->To)
  val v1 = HOLVar("x", Ti)
  val f1 = Atom(c1,v1::Nil)
  val ax = Axiom(f1::Nil, f1::Nil)
  val a1 = ax // Axiom return a pair of the proof and a mapping and we want only the proof here
  val c2 = HOLVar("b", Ti->To)
  val v2 = HOLVar("c", Ti)
  val f2 = Atom(c1,v1::Nil)
  val f3 = Atom(HOLVar("e", To))
  val a2 = Axiom(f2::f3::Nil, f2::f3::Nil)
  val a3 = Axiom(f2::f2::f3::Nil, f2::f2::f3::Nil)
  val ap = Axiom(f1::f1::Nil, Nil)
  val a4 = ap
  val pr = WeakeningRightRule( ax, f1 )
  val pr1 = OrRightRule( pr, f1, f1 )
  val pr2 = WeakeningLeftRule( ax, f1 )
  val pr3 = AndLeftRule( pr2, f1, f1 )

  "The factories/extractors for LK" should {

    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        (a1) must beLike {case Axiom(Sequent(x,y)) => (x(0).formula == f1) && (y(0).formula == f1) must_== true}
      }
      "- Same formulas on the same side must become different occurrences" in {
        val ant = a4.root.antecedent.toList
        (ant.length) must beEqualTo(2)
        (ant.head) must not be(ant.last)
      }
    }

    "work for WeakeningLeftRule" in {
      val a = WeakeningLeftRule(a2, f1)
      val (up1, Sequent(x,y), prin1) = WeakeningLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (f1)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent).toList.map(x => x.formula))
      }
    }

    "work for WeakeningRightRule" in {
      val a = WeakeningRightRule(a2, f1)
      val (up1, Sequent(x,y), prin1) = WeakeningRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (f1)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent).toList.map(x => x.formula))
      }
    }

    "work for ContractionLeftRule" in {
      val a = ContractionLeftRule(a3, a3.root.antecedent(0), a3.root.antecedent(1))
      val (up1,  Sequent(x,y), aux1, aux2, prin1) = ContractionLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (f2)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x.map(x => x.formula)) must contain(prin1.formula)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(x => x.formula).filter(y => y == aux1.formula)) must be_!=(2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.filterNot(_ == aux1).filterNot(_ == aux2)).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent).toList.map(x => x.formula))
      }
    }

    "work for ContractionRightRule" in {
      val a = ContractionRightRule(a3, a3.root.succedent(0),a3.root.succedent(1))
      val (up1,  Sequent(x,y), aux1, aux2, prin1) = ContractionRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (f2)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y.map(x => x.formula)) must contain(prin1.formula)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.map(y => y.formula).filter(x => x == aux1.formula)) must be_!=(2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.filterNot(_ == aux1).filterNot(_ == aux2)).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent).toList.map(x => x.formula))
      }
    }

    "work for CutRule" in {
      val a = CutRule(a2, a3, a2.root.succedent(0), a3.root.antecedent(0))
      val (up1, up2, Sequent(x,y), aux1, aux2) = CutRule.unapply(a).get
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.filter(z => z.formula == f2)).size must beEqualTo(2)
        (x.filter(z => z.formula == f2)).size must beEqualTo(2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y).map(x => x.formula)) must beEqualTo (((up1.root.succedent.filterNot(_ == aux1)) ++ up2.root.succedent).map(x => x.formula))
        ((x).map(x => x.formula)) must beEqualTo ((up1.root.antecedent ++ (up2.root.antecedent.filterNot(_ == aux2))).map(x => x.formula))
      }
    }

    "work for AndRightRule" in {
      val a = AndRightRule(a1, a2, f1, f2)
      val (up1, up2, Sequent(x,y), aux1, aux2, prin1) = AndRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (And(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.map(z => z.formula)) must not contain(f1)
        (y.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (x.toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.toList ++ up2.root.antecedent.toList).map(x => x.formula))
        ((y.toList.map(x => x.formula).filterNot(x => x == And(f1,f2)))) must beEqualTo (((up1.root.succedent.filterNot(_ == aux1)).toList ++ (up2.root.succedent.filterNot(_ ==  aux2)).toList).map(x => x.formula))
      }
    }

    "work for AndLeft1Rule" in {
      val a = AndLeft1Rule(a2, f2, f1)
      val (up1,  Sequent(x,y), aux1, prin1) = AndLeft1Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (And(f2,f1))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.filterNot(_ == aux1)).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent).toList.map(x => x.formula))
      }
    }

    "work for AndLeft2Rule" in {
      val a = AndLeft2Rule(a2, f1, f2)
      val (up1,  Sequent(x,y), aux1, prin1) = AndLeft2Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (And(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(z => z.formula)) must not contain(f1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.filterNot(_ == aux1)).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent).toList.map(x => x.formula))
      }
    }

    "work for AndLeftRule" in {
      val a = AndLeftRule(a2, f1, f3)
      "- Principal formula is created correctly" in {
        (a.prin.head.formula) must beEqualTo (And(f1,f3))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (a.root.antecedent) must contain(a.prin.head)
      }

      "- Lower sequent must not contain the auxiliary formulas" in {
        (a.root.antecedent) must not (contain(f1))
        (a.root.antecedent) must not (contain(f3))
      }

      "- Principal formula is created correctly when auxiliary formulas are equal" in {
        (pr3.prin.head.formula) must beEqualTo (And(f1,f1))
      }

      "- Lower sequent must not contain the auxiliary formulas when auxiliary formulas are equal" in {
        (pr3.root.antecedent) must not (contain(f1))
      }
    }

    "work for OrLeftRule" in {
      val a = OrLeftRule(a1, a2, f1, f2)
      val (up1, up2, Sequent(x,y), aux1, aux2, prin1) = OrLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Or(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(z => z.formula)) must not contain(f1)
        (x.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (y.toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.toList ++ up2.root.succedent.toList).map(x => x.formula))
        ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo (((up1.root.antecedent.filterNot(_ == aux1)).toList ++ (up2.root.antecedent .filterNot(_ == aux2)).toList).map(x => x.formula))
      }

      "- Descendants must be correctly computed" in {
        "(1)" in {
          // get descendant of occurrence of left auxiliary formula
          a.getDescendantInLowerSequent(a1.root.antecedent(0)) must beLike {
            case Some(x) => x.formula == Or(f1, f2) must_== true
            case None => ko
          }
        }
        "(2)" in {
          // get descendant of occurrence of left premise context in succedent
          a.getDescendantInLowerSequent(a1.root.succedent(0)) must beLike {
            case Some(x) => x.formula == f1 must_== true
            case None => ko
          }
        }
      }
    }

    "work for OrRightRule" in {
      "- Principal formula is created correctly when auxiliary formulas are equal" in {
        (pr1.prin.head.formula) must beEqualTo (Or(f1,f1))
      }

      "- Lower sequent must not contain the auxiliary formulas when auxiliary formulas are equal" in {
        (pr1.root.succedent) must not (contain(f1))
      }
    }

    "work for OrRight1Rule" in {
      val a = OrRight1Rule(a2, f2, f1)
      val (up1,  Sequent(x,y), aux1, prin1) = OrRight1Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Or(f2,f1))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.filterNot(_ == aux1)).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent).toList.map(x => x.formula))
      }
    }

    "work for OrRight2Rule" in {
      val a = OrRight2Rule(a2, f1, f2)
      val (up1,  Sequent(x,y), aux1, prin1) = OrRight2Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Or(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.map(z => z.formula)) must not contain(f1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.filterNot(_ == aux1)).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent).toList.map(x => x.formula))
      }
    }

    "work for ImpLeftRule" in {
      val a = ImpLeftRule(a1, a2, f1, f2)
      val (up1, up2, Sequent(x,y), aux1, aux2, prin1) = ImpLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Imp(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.filter(z => z.formula == f1)).size must beEqualTo(1)
        (x.filter(z => z.formula == f2)).size must beEqualTo(1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        "1" in { (y.toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.filterNot(_ == aux1).toList ++ (up2.root.succedent).toList).map(x => x.formula))}
        "2" in { ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.toList ++ (up2.root.antecedent.filterNot(_ == aux2)).toList).map(x => x.formula))}
      }
    }

    "work for ImpRightRule" in {
      val a = ImpRightRule(a2, f2, f2)
      val (up1,  Sequent(x,y), aux1, aux2, prin1) = ImpRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Imp(f2,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(z => z.formula)) must not contain(f2)
        (y.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        "1" in { ((y.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.filterNot(_ == aux2)).toList.map(x => x.formula))}
        "2" in { ((x).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.filterNot(_ == aux1)).toList.map(x => x.formula))}
      }
    }

    "work for NegRightRule" in {
      val a = NegRightRule(a2, f2)
      val (up1,  Sequent(x,y), aux1, prin1) = NegRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Neg(f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent.filterNot(_ == aux1)).toList.map(x => x.formula))
      }
    }

    "work for NegLeftRule" in {
      val a = NegLeftRule(a2, f2)
      val (up1, Sequent(x,y), aux1, prin1) = NegLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (Neg(f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.map(z => z.formula)) must not contain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x.filterNot(_ == prin1)).toList.map(x => x.formula)) must beEqualTo ((up1.root.antecedent).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqualTo ((up1.root.succedent.filterNot(_ == aux1)).toList.map(x => x.formula))
      }
    }

    "work for ForallLeftRule" in {
      val q = HOLVar( "q", Ti -> To )
      val x = HOLVar( "X", Ti )
      val subst = HOLAbs( x, HOLApp( q, x ) ) // lambda x. q(x)
      val p = HOLVar( "p", (Ti -> To) -> To )
      val a = HOLVar( "a", Ti )
      val qa = Atom( q, a::Nil )
      val pl = Atom( p, subst::Nil )
      val aux = Or( pl, qa )                  // p(lambda x. q(x)) or q(a)
      val z = HOLVar( "Z", Ti -> To )
      val pz = Atom( p, z::Nil )
      val za = Atom( z, a::Nil )
      val main = AllVar( z, Or( pz, za ) )    // forall lambda z. p(z) or z(a)
      val ax = Axiom(aux::Nil, Nil)
      val rule = ForallLeftRule(ax, aux, main, subst)
      val (up1,  Sequent(ant,succ), aux1, prin1, term) = ForallLeftRule.unapply(rule).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (main)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (ant) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (ant) must not contain(aux1)
      }
    }

    "work for ForallRightRule" in {
      val x = HOLVar( "X", Ti -> To)            // eigenvar
      val p = HOLVar( "p", (Ti -> To) -> To )
      val a = HOLVar( "a", Ti )
      val xa = Atom( x, a::Nil )
      val px = Atom( p, x::Nil )
      val aux = Or( px, xa )                  // p(x) or x(a)
      val z = HOLVar( "Z", Ti -> To )
      val pz = Atom( p, z::Nil )
      val za = Atom( z, a::Nil )
      val main = AllVar( z, Or( pz, za ) )    // forall lambda z. p(z) or z(a)
      val ax = Axiom(Nil, aux::Nil )
      val rule = ForallRightRule(ax, aux, main, x)
      val (up1,  Sequent(ant,succ), aux1, prin1, ev) = ForallRightRule.unapply(rule).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqualTo (main)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (succ) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (succ) must not contain(aux1)
      }
    }

    "work for weak quantifier rules" in {
      val List(x,y,z) = List(("x", Ti->Ti),("y",Ti->Ti) ,("z", Ti->Ti)) map (u => HOLVar(u._1,u._2))
      val List(p,a,b) = List(("P", (Ti->Ti) -> ((Ti->Ti) -> ((Ti->Ti) -> To))),
                             ("a", Ti->Ti) ,
                             ("b", Ti->Ti)) map (u => HOLConst(u._1,u._2))
      val paba = Atom(p,List(a,b,a))
      val pxba = Atom(p,List(x,b,a))
      val expxba = ExVar(x,pxba)
      val allpxba = AllVar(x,pxba)

      val ax1 = Axiom(paba::Nil, Nil)
      ForallLeftRule(ax1, ax1.root.occurrences(0), allpxba, a).root.occurrences(0).formula must_==(allpxba)

      ForallLeftRule(ax1, ax1.root.occurrences(0), allpxba, b).root.occurrences(0).formula must_==(allpxba) must throwAn[Exception]()

      val ax2 = Axiom(Nil, paba::Nil)
      ExistsRightRule(ax2, ax2.root.occurrences(0), expxba, a).root.occurrences(0).formula must_==(expxba)
      ExistsRightRule(ax2, ax2.root.occurrences(0), expxba, b).root.occurrences(0).formula must_==(expxba) must throwAn[Exception]()
    }

    "work for first order proofs (1)" in {
      val List(a,b) = List("a","b") map (FOLConst(_))
      val List(x,y) = List("x","y") map (FOLVar(_))
      val p = "P"
      val pay = FOLAtom(p, List(a,y))
      val allxpax = FOLAllVar(x,FOLAtom(p, List(a,x)))
      val ax = Axiom(List(pay), List(pay))
      val i1 = ForallLeftRule(ax, ax.root.antecedent(0), allxpax, y)
      val i2 = ForallRightRule(i1, i1.root.succedent(0), allxpax, y)
      val i3 = OrRight1Rule(i2, i2.root.succedent(0), pay)

      i2.root.toFSequent match {
        case FSequent(List(f1), List(f2)) =>
          f1 mustEqual(allxpax)
          f2 mustEqual(allxpax)
          f1 must beAnInstanceOf[FOLFormula]
          f2 must beAnInstanceOf[FOLFormula]
        case fs @ _ =>
          ko("Wrong result sequent "+fs)
      }

      i3.root.toFSequent.formulas map (_ must beAnInstanceOf[FOLFormula])
    }

    "work for first order proofs (2)" in {
      val List(a,b) = List("a","b") map (FOLConst(_))
      val List(x,y) = List("x","y") map (FOLVar(_))
      val p = "P"
      val pay = FOLAtom(p, List(a,y))
      val allxpax = FOLExVar(x,FOLAtom(p, List(a,x)))
      val ax = Axiom(List(pay), List(pay))
      val i1 = ExistsRightRule(ax, ax.root.succedent(0), allxpax, y)
      val i2 = ExistsLeftRule(i1, i1.root.antecedent(0), allxpax, y)
      i2.root.toFSequent match {
        case FSequent(List(f1), List(f2)) =>
          f1 mustEqual(allxpax)
          f2 mustEqual(allxpax)
          f1 must beAnInstanceOf[FOLFormula]
          f2 must beAnInstanceOf[FOLFormula]
        case fs @ _ =>
          ko("Wrong result sequent "+fs)
      }
    }

  }

  "Equality rules" should {
    val (s, t) = (HOLConst("s", Ti), HOLConst("t", Ti))
    val P = HOLConst("P", Ti -> To)
    val Q = HOLConst("Q", Ti -> (Ti -> To))
    val est = Equation(s, t)
    val Ps = Atom(P, List(s))
    val Pt = Atom (P, List(t))

    val Qss = Atom(Q, List(s,s))
    val Qst = Atom(Q, List(s,t))
    val Qts = Atom(Q, List(t,s))
    val Qtt = Atom(Q, List(t,t))

    val ax1 = Axiom(List(est), List(est))
    val ax2 = Axiom(List(Ps), List(Ps))
    val ax3 = Axiom(List(Pt), List(Pt))
    val ax4 = Axiom(List(Qss), List(Qss))
    val ax5 = Axiom(List(Qtt), List(Qtt))

    "refuse first auxiliary formulas that are not equations" in {
      EquationLeft1Rule(ax3, ax2, ax3.root.succedent.head, ax2.root.antecedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
      EquationLeft2Rule(ax3, ax2, ax3.root.succedent.head, ax2.root.antecedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
      EquationRight1Rule(ax3, ax2, ax3.root.succedent.head, ax2.root.succedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
      EquationRight2Rule(ax3, ax2, ax3.root.succedent.head, ax2.root.succedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
    }

    "refuse when the wrong term is at the target position" in {
      EquationLeft1Rule(ax1, ax3, ax1.root.succedent.head, ax3.root.antecedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
      EquationLeft2Rule(ax1, ax2, ax1.root.succedent.head, ax2.root.antecedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
      EquationRight1Rule(ax1, ax3, ax1.root.succedent.head, ax3.root.succedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
      EquationRight2Rule(ax1, ax2, ax1.root.succedent.head, ax2.root.succedent.head, HOLPosition(2)) must throwAn[LKRuleCreationException]
    }

    "refuse when auxiliary formula cannot be transformed to main formula in one step" in {
      EquationLeft1Rule(ax1, ax4, ax1.root.succedent.head, ax4.root.antecedent.head, Qtt) must throwAn[LKRuleCreationException]
      EquationLeft2Rule(ax1, ax5, ax1.root.succedent.head, ax5.root.antecedent.head, Qss) must throwAn[LKRuleCreationException]
      EquationRight1Rule(ax1, ax4, ax1.root.succedent.head, ax4.root.succedent.head, Qtt) must throwAn[LKRuleCreationException]
      EquationRight2Rule(ax1, ax5, ax1.root.succedent.head, ax5.root.succedent.head, Qss) must throwAn[LKRuleCreationException]
    }

    "correctly perform replacements" in {

      val sequent1 = FSequent(List(est, Qst), List(Qss))
      val sequent2 = FSequent(List(est, Qts), List(Qss))

      val sequent3 = FSequent(List(est, Qts), List(Qtt))
      val sequent4 = FSequent(List(est, Qst), List(Qtt))

      val sequent5 = FSequent(List(est, Qss), List(Qst))
      val sequent6 = FSequent(List(est, Qss), List(Qts))

      val sequent7 = FSequent(List(est, Qtt), List(Qts))
      val sequent8 = FSequent(List(est, Qtt), List(Qst))

      EquationLeft1Rule(ax1, ax4, ax1.root.succedent.head, ax4.root.antecedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent1)
      EquationLeft1Rule(ax1, ax4, ax1.root.succedent.head, ax4.root.antecedent.head, Qts).root.toFSequent must beEqualTo(sequent2)

      EquationLeft2Rule(ax1, ax5, ax1.root.succedent.head, ax5.root.antecedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent3)
      EquationLeft2Rule(ax1, ax5, ax1.root.succedent.head, ax5.root.antecedent.head, Qst).root.toFSequent must beEqualTo(sequent4)

      EquationRight1Rule(ax1, ax4, ax1.root.succedent.head, ax4.root.succedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent5)
      EquationRight1Rule(ax1, ax4, ax1.root.succedent.head, ax4.root.succedent.head, Qts).root.toFSequent must beEqualTo(sequent6)

      EquationRight2Rule(ax1, ax5, ax1.root.succedent.head, ax5.root.succedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent7)
      EquationRight2Rule(ax1, ax5, ax1.root.succedent.head, ax5.root.succedent.head, Qst).root.toFSequent must beEqualTo(sequent8)
    }
  }

  "Weakening macro rules" should {
    val x = FOLVar("x")
    val y = FOLVar("y")

    val Px = FOLAtom("P", List(x))
    val Py = FOLAtom("P", List(y))

    val ax = Axiom(List(Px), List(Px))
    "perform zero weakenings" in {

      WeakeningLeftMacroRule(ax, Nil)  must beEqualTo(ax)
      WeakeningRightMacroRule(ax, Nil) must beEqualTo(ax)
      WeakeningMacroRule(ax, Nil, Nil) must beEqualTo(ax)
    }

    "correctly perform multiple weakenings" in {
      val proof  = WeakeningRightRule(WeakeningLeftRule(WeakeningLeftRule(ax, Py), Neg(Py)), Py)

      WeakeningMacroRule(ax, List(Neg(Py),Py), List(Py)).root.toFSequent.multiSetEquals(proof.root.toFSequent) must beTrue
    }
  }

  "Contraction macro rules" should {
    val x = FOLVar("x")
    val y = FOLVar("y")

    val Px = FOLAtom("P", List(x))
    val Py = FOLAtom("P", List(y))

    val ax = Axiom(List(Px), List(Px))

    "perform zero contractions" in {
      ContractionLeftMacroRule(ax, Nil) must beEqualTo(ax)
      ContractionLeftMacroRule(ax, List(ax.root.antecedent.head)) must beEqualTo(ax)
      ContractionRightMacroRule(ax, Nil) must beEqualTo(ax)
      ContractionRightMacroRule(ax, List(ax.root.succedent.head)) must beEqualTo(ax)
    }

    "return the original proof if there is nothing to do" in {
      ContractionLeftMacroRule(ax, Px).root.toFSequent must beEqualTo(ax.root.toFSequent)
      ContractionLeftMacroRule(ax, Py).root.toFSequent must beEqualTo(ax.root.toFSequent)
      ContractionRightMacroRule(ax, Px).root.toFSequent must beEqualTo(ax.root.toFSequent)
      ContractionRightMacroRule(ax, Py).root.toFSequent must beEqualTo(ax.root.toFSequent)
    }

    "correctly perform multiple contractions" in {
      val ax2 = Axiom(List(Px, Px, Py, Px), List(Px, Neg(Px), Neg(Px)))

      val sequent1 = FSequent(List(Py, Px), List(Px, Neg(Px), Neg(Px)))
      val sequent2 = FSequent(List(Px, Px, Py, Px), List(Px, Neg(Px)))
      ContractionLeftMacroRule(ax2, Px).root.toFSequent must beEqualTo(sequent1)
      ContractionRightMacroRule(ax2, Neg(Px)).root.toFSequent must beEqualTo(sequent2)
    }
  }

  "Equality macro rules" should {
    val (s, t) = (HOLConst("s", Ti), HOLConst("t", Ti))
    val P = HOLConst("P", Ti -> To)
    val Q = HOLConst("Q", Ti -> (Ti -> To))
    val est = Equation(s, t)
    val Ps = Atom(P, List(s))
    val Pt = Atom (P, List(t))

    val Qss = Atom(Q, List(s,s))
    val Qst = Atom(Q, List(s,t))
    val Qts = Atom(Q, List(t,s))
    val Qtt = Atom(Q, List(t,t))

    val ax1 = Axiom(List(est), List(est))
    val ax2 = Axiom(List(Ps), List(Ps))
    val ax3 = Axiom(List(Pt), List(Pt))
    val ax4 = Axiom(List(Qss), List(Qss))
    val ax5 = Axiom(List(Qtt), List(Qtt))

    val eq = ax1.root.succedent.head

    "choose the right rule to use" in {
      val sequent1 = FSequent(List(est, Ps), List(Pt))
      val sequent2 = FSequent(List(est, Pt), List(Ps))

      EquationLeftRule(ax1, ax3, eq, ax3.root.antecedent.head, Ps).root.toFSequent must beEqualTo(sequent1)
      EquationLeftRule(ax1, ax2, eq, ax2.root.antecedent.head, Pt).root.toFSequent must beEqualTo(sequent2)

      EquationRightRule(ax1, ax2, eq, ax2.root.succedent.head, Pt).root.toFSequent must beEqualTo(sequent1)
      EquationRightRule(ax1, ax3, eq, ax3.root.succedent.head, Ps).root.toFSequent must beEqualTo(sequent2)

      EquationLeftRule(ax1, ax3, eq, ax3.root.antecedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent1)
      EquationLeftRule(ax1, ax2, eq, ax2.root.antecedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent2)

      EquationRightRule(ax1, ax2, eq, ax2.root.succedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent1)
      EquationRightRule(ax1, ax3, eq, ax3.root.succedent.head, HOLPosition(2)).root.toFSequent must beEqualTo(sequent2)
    }

    "perform correctly if there is only one replacement to be made" in {

      val sequent1 = FSequent(List(est, Qst), List(Qss))
      val sequent2 = FSequent(List(est, Qts), List(Qss))

      val sequent3 = FSequent(List(est, Qts), List(Qtt))
      val sequent4 = FSequent(List(est, Qst), List(Qtt))

      val sequent5 = FSequent(List(est, Qss), List(Qst))
      val sequent6 = FSequent(List(est, Qss), List(Qts))

      val sequent7 = FSequent(List(est, Qtt), List(Qts))
      val sequent8 = FSequent(List(est, Qtt), List(Qst))

      val proof1 = EquationLeftMacroRule(ax1, ax4, eq, ax4.root.antecedent.head, Nil, List(HOLPosition(2)))
      val proof2 = EquationLeftMacroRule(ax1, ax4, eq, ax4.root.antecedent.head, Qts)
      val proof3 = EquationLeftMacroRule(ax1, ax5, eq, ax5.root.antecedent.head, List(HOLPosition(2)), Nil)
      val proof4 = EquationLeftMacroRule(ax1, ax5, eq, ax5.root.antecedent.head, Qst)
      val proof5 = EquationRightMacroRule(ax1, ax4, eq, ax4.root.succedent.head, Nil, List(HOLPosition(2)))
      val proof6 = EquationRightMacroRule(ax1, ax4, eq, ax4.root.succedent.head, Qts)
      val proof7 = EquationRightMacroRule(ax1, ax5, eq, ax5.root.succedent.head, List(HOLPosition(2)), Nil)
      val proof8 = EquationRightMacroRule(ax1, ax5, eq, ax5.root.succedent.head, Qst)

      proof1.root.toFSequent must beEqualTo(sequent1)
      proof2.root.toFSequent must beEqualTo(sequent2)

      proof3.root.toFSequent must beEqualTo(sequent3)
      proof4.root.toFSequent must beEqualTo(sequent4)

      proof5.root.toFSequent must beEqualTo(sequent5)
      proof6.root.toFSequent must beEqualTo(sequent6)

      proof7.root.toFSequent must beEqualTo(sequent7)
      proof8.root.toFSequent must beEqualTo(sequent8)
    }

    "perform correctly when several replacements are made" in {
      val sequent1 = FSequent(List(est, Qtt), List(Qss))
      val sequent2 = FSequent(List(est, Qss), List(Qtt))

      val proof1 = EquationLeftMacroRule(ax1, ax4, eq, ax4.root.antecedent.head, Qtt)
      val proof2 = EquationLeftMacroRule(ax1, ax5, eq, ax5.root.antecedent.head, Qss)
      val proof3 = EquationRightMacroRule(ax1, ax4, eq, ax4.root.succedent.head, Qtt)
      val proof4 = EquationRightMacroRule(ax1, ax5, eq, ax5.root.succedent.head, Qss)

      proof1.root.toFSequent must beEqualTo(sequent1)
      proof2.root.toFSequent must beEqualTo(sequent2)
      proof3.root.toFSequent must beEqualTo(sequent2)
      proof4.root.toFSequent must beEqualTo(sequent1)

    }
  }
/*

  "Unary equality rules" should {
    val (s, t) = (HOLConst("s", Ti), HOLConst("t", Ti))
    val P = HOLConst("P", Ti -> To)
    val Q = HOLConst("Q", Ti -> (Ti -> To))
    val est = Equation(s, t)
    val Ps = Atom(P, List(s))
    val Pt = Atom (P, List(t))

    val Qss = Atom(Q, List(s,s))
    val Qst = Atom(Q, List(s,t))
    val Qts = Atom(Q, List(t,s))
    val Qtt = Atom(Q, List(t,t))

    val ax1 = Axiom(List(est), List(est))
    val ax2 = Axiom(List(Ps), List(Ps))
    val ax3 = Axiom(List(Pt), List(Pt))
    val ax4 = Axiom(List(Qss), List(Qss))
    val ax5 = Axiom(List(Qtt), List(Qtt))

    val eq = ax1.root.succedent.head

    "work correctly in simple cases" in {
      val seq1 = FSequent(List(est, Pt), List(Ps))
      val seq2 = FSequent(List(est, Ps), List(Pt))

      val subProof1 = WeakeningLeftRule(ax2, est)
      val proof1 = UnaryEquationLeft1Rule(subProof1, subProof1.prin(0), subProof1.root.antecedent(0), HOLPosition(2))

      (proof1.root.toFSequent multiSetEquals seq1) must beTrue

      val subProof2 = WeakeningLeftRule(ax3, est)
      val proof2 = UnaryEquationLeft2Rule(subProof2, subProof2.prin(0), subProof2.root.antecedent(0), HOLPosition(2))

      (proof2.root.toFSequent multiSetEquals seq2) must beTrue

      val subProof3 = WeakeningLeftRule(ax2, est)
      val proof3 = UnaryEquationRight1Rule(subProof3, subProof3.prin(0), subProof3.root.succedent(0), HOLPosition(2))

      (proof3.root.toFSequent multiSetEquals seq2) must beTrue

      val subProof4 = WeakeningLeftRule(ax3, est)
      val proof4 = UnaryEquationRight2Rule(subProof4, subProof4.prin(0), subProof4.root.succedent(0), HOLPosition(2))

      (proof4.root.toFSequent multiSetEquals seq1) must beTrue
    }

    "be correctly converted to binary rules" in {
      val subProof1 = WeakeningLeftRule(ax2, est)
      val proof1 = UnaryEquationLeft1Rule(subProof1, subProof1.prin(0), subProof1.root.antecedent(0), HOLPosition(2))

     EquationRuleConverter.toBinary(proof1)

      val subProof2 = WeakeningLeftRule(ax3, est)
      val proof2 = UnaryEquationLeft2Rule(subProof2, subProof2.prin(0), subProof2.root.antecedent(0), HOLPosition(2))

      EquationRuleConverter.toBinary(proof2)

      val subProof3 = WeakeningLeftRule(ax2, est)
      val proof3 = UnaryEquationRight1Rule(subProof3, subProof3.prin(0), subProof3.root.succedent(0), HOLPosition(2))

      EquationRuleConverter.toBinary(proof3)

      val subProof4 = WeakeningLeftRule(ax3, est)
      val proof4 = UnaryEquationRight2Rule(subProof4, subProof4.prin(0), subProof4.root.succedent(0), HOLPosition(2))

      EquationRuleConverter.toBinary(proof4)

      ok
    }
  }
*/

}

