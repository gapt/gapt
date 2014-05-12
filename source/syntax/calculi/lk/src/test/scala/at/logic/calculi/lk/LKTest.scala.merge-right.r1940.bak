/*
* LKTest.scala
*
* To change this template, choose Tools | Template Manager
* and open the template in the editor.
*/

package at.logic.calculi.lk

import at.logic.language.lambda.substitutions.Substitution
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._
import propositionalRules._
import base._
import quantificationRules._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.calculi.lk.lkSpecs.beMultisetEqual
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.symbols.VariableStringSymbol
import macroRules._

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

  val c1 = HOLVar("a", i->o)
  val v1 = HOLVar("x", i)
  val f1 = HOLAppFormula(c1,v1)
  val ax = Axiom(f1::Nil, f1::Nil)
  val a1 = ax // Axiom return a pair of the proof and a mapping and we want only the proof here
  val c2 = HOLVar("b", i->o)
  val v2 = HOLVar("c", i)
  val f2 = HOLAppFormula(c1,v1)
  val f3 = HOLVarFormula("e")
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
        //(a.root.antecedent) must contain(And(f1,f3)) // occurrences are compared and therefore the test fails
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
      val q = HOLVar( "q", i -> o )
      val x = HOLVar( "X", i )
      val subst = HOLAbs( x, HOLApp( q, x ) ) // lambda x. q(x)
      val p = HOLVar( "p", (i -> o) -> o )
      val a = HOLVar( "a", i )
      val qa = HOLAppFormula( q, a )
      val pl = HOLAppFormula( p, subst )
      val aux = Or( pl, qa )                  // p(lambda x. q(x)) or q(a)
      val z = HOLVar( "Z", i -> o )
      val pz = HOLAppFormula( p, z )
      val za = HOLAppFormula( z, a )
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
      /*"- Lower sequent must not contain the auxiliary formulas" in {
        (ant) must not contain(aux1)
      }     */
    }

    "work for ForallRightRule" in {
      val x = HOLVar( "X", i -> o)            // eigenvar
      val p = HOLVar( "p", (i -> o) -> o )
      val a = HOLVar( "a", i )
      val xa = HOLAppFormula( x, a )
      val px = HOLAppFormula( p, x )
      val aux = Or( px, xa )                  // p(x) or x(a)
      val z = HOLVar( "Z", i -> o )
      val pz = HOLAppFormula( p, z )
      val za = HOLAppFormula( z, a )
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
      /*"- Lower sequent must not contain the auxiliary formulas" in {
        (succ) must not contain(aux1)
      } */
    }

    "work for weak quantifier rules" in {
      val List(x,y,z) = List(("x", i->i),("y",i->i) ,("z", i->i)) map (u => HOLVar(VariableStringSymbol(u._1),u._2))
      val List(p,a,b) = List(("P", (i->i) -> ((i->i) -> ((i->i) -> o))),
                             ("a", i->i) ,
                             ("b", i->i)) map (u => HOLConst(ConstantStringSymbol(u._1),u._2))
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

  }
}
