/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import org.specs._
import org.specs.runner._

import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols._
import propositionalRules._
import base._
import propositionalRules.ImplicitConverters._
import quantificationRules._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.calculi.lk.lkSpecs.beMultisetEqual
import at.logic.language.lambda.symbols.ImplicitConverters._
import scala.collection.immutable._
import at.logic.language.lambda.symbols.VariableStringSymbol

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
class LKTest extends SpecificationWithJUnit {
  val c1 = HOLVar("a", i->o)
  val v1 = HOLVar("x", i)
  val f1 = HOLAppFormula(c1,v1)
  val ax = Axiom(Sequent(f1::Nil, f1::Nil))
  val a1 = ax._1 // Axiom return a pair of the proof and a mapping and we want only the proof here
  val c2 = HOLVar("b", i->o)
  val v2 = HOLVar("c", i)
  val f2 = HOLAppFormula(c1,v1)
  val f3 = HOLVarFormula("e")
  val a2 = Axiom(Sequent(f2::f3::Nil, f2::f3::Nil))
  val a3 = Axiom(Sequent(f2::f2::f3::Nil, f2::f2::f3::Nil))
  val ap = Axiom(Sequent(f1::f1::Nil, Nil))
  val a4 = ap._1

  "The factories/extractors for LK" should {

    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        (a1) must beLike {case Axiom(SequentOccurrence(x,y)) => (x.toArray(0).formula == f1) && (y.toArray(0).formula == f1)}
      }
      "- Same formulas on the same side must become different occurrences" in {
        val ant = a4.root.antecedent.toList
        (ant.length) must beEqual(2)
        (ant.first) must notBe(ant.last)
      }
      "- FormulaOccurrence mapping must be correct" in {
        val map = ap._2._1
        (map.first) must notBe(map.last)
        (map.filter( o => o != map.first ) ).length must beEqual(1)
      }
    }

    "work for WeakeningLeftRule" in {
      val a = WeakeningLeftRule(a2, f1)
      val (up1, SequentOccurrence(x,y), prin1) = WeakeningLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (f1)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (x - prin1) must beDifferent ((up1.root.antecedent))
        ((y)) must beDifferent ((up1.root.succedent))
      }
    }

    "work for WeakeningRightRule" in {
      val a = WeakeningRightRule(a2, f1)
      val (up1, SequentOccurrence(x,y), prin1) = WeakeningRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (f1)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent))
        ((x)) must beDifferent ((up1.root.antecedent))
      }
    }

    "work for ContractionLeftRule" in {
      val a = ContractionLeftRule(a3, f2)
      val (up1,  SequentOccurrence(x,y), aux1, aux2, prin1) = ContractionLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (f2)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x) must notContain(aux1)
        (x) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1 - aux2).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (x - prin1) must beDifferent ((up1.root.antecedent  - aux1 - aux2))
        ((y)) must beDifferent ((up1.root.succedent))
      }
    }

    "work for ContractionRightRule" in {
      val a = ContractionRightRule(a3, f2)
      val (up1,  SequentOccurrence(x,y), aux1, aux2, prin1) = ContractionRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (f2)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
        (y) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1 - aux2).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent  - aux1 - aux2))
        (x) must beDifferent ((up1.root.antecedent))
      }
    }

    "work for CutRule" in {
      val a = CutRule(a2, a3, f2)
      val (up1, up2, SequentOccurrence(x,y), aux1, aux2) = CutRule.unapply(a).get
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
        (x) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y).toList.map(x => x.formula)) must beEqual (((up1.root.succedent - aux1) ++ up2.root.succedent).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent ++ (up2.root.antecedent - aux2)).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y) must beDifferent ((up1.root.succedent - aux1) ++ up2.root.succedent)
        (x) must beDifferent (up1.root.antecedent ++ (up2.root.antecedent - aux2))
      }
    }

    "work for AndRightRule" in {
      val a = AndRightRule(a1, a2, f1, f2)
      val (up1, up2, SequentOccurrence(x,y), aux1, aux2, prin1) = AndRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (And(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
        (y) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (x.toList.map(x => x.formula)) must beEqual ((up1.root.antecedent ++ up2.root.antecedent).toList.map(x => x.formula))
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent ++ up2.root.succedent - aux1 - aux2).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (x) must beDifferent ((up1.root.antecedent ++ up2.root.antecedent))
        ((y - prin1)) must beDifferent ((up1.root.succedent ++ up2.root.succedent - aux1 - aux2))
      }
    }

    "work for AndLeft1Rule" in {
      val a = AndLeft1Rule(a2, f2, f1)
      val (up1,  SequentOccurrence(x,y), aux1, prin1) = AndLeft1Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (And(f2,f1))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x) must notContain(aux1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (x - prin1) must beDifferent ((up1.root.antecedent  - aux1))
        ((y)) must beDifferent ((up1.root.succedent))
      }
    }

    "work for AndLeft2Rule" in {
      val a = AndLeft2Rule(a2, f1, f2)
      val (up1,  SequentOccurrence(x,y), aux1, prin1) = AndLeft2Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (And(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x) must notContain(aux1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (x - prin1) must beDifferent ((up1.root.antecedent  - aux1))
        ((y)) must beDifferent ((up1.root.succedent))
      }
    }

    "work for OrLeftRule" in {
      val a = OrLeftRule(a1, a2, f1, f2)
      val (up1, up2, SequentOccurrence(x,y), aux1, aux2, prin1) = OrLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Or(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x) must notContain(aux1)
        (x) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (y.toList.map(x => x.formula)) must beEqual ((up1.root.succedent ++ up2.root.succedent).toList.map(x => x.formula))
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent ++ up2.root.antecedent - aux1 - aux2).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y) must beDifferent ((up1.root.succedent ++ up2.root.succedent))
        ((x - prin1)) must beDifferent ((up1.root.antecedent ++ up2.root.antecedent - aux1 - aux2))
      }
      "- Descendants must be correctly computed" in {
        "(1)" in {
          // get descendant of occurrence of left auxiliary formula
          a.getDescendantInLowerSequent(ax._2._1.first) must beLike {
            case Some(x) => x == prin1 && x.formula == Or(f1, f2)
            case None => false
          }
        }
        "(2)" in {
          // get descendant of occurrence of left premise context in succedent
          a.getDescendantInLowerSequent(ax._2._2.first) must beLike {
            case Some(x) => x.formula == f1
            case None => false
          }
        }
      }
    }

    "work for OrRight1Rule" in {
      val a = OrRight1Rule(a2, f2, f1)
      val (up1,  SequentOccurrence(x,y), aux1, prin1) = OrRight1Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Or(f2,f1))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent  - aux1))
        ((x)) must beDifferent ((up1.root.antecedent))
      }
    }

    "work for OrRight2Rule" in {
      val a = OrRight2Rule(a2, f1, f2)
      val (up1,  SequentOccurrence(x,y), aux1, prin1) = OrRight2Rule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Or(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent  - aux1))
        ((x)) must beDifferent ((up1.root.antecedent))
      }
    }

    "work for ImpLeftRule" in {
      val a = ImpLeftRule(a1, a2, f1, f2)
      val (up1, up2, SequentOccurrence(x,y), aux1, aux2, prin1) = ImpLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Imp(f1,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
        (x) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (y.toList.map(x => x.formula)) must beEqual ((up1.root.succedent ++ up2.root.succedent - aux1).toList.map(x => x.formula))
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent ++ up2.root.antecedent - aux2).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y) must beDifferent ((up1.root.succedent ++ up2.root.succedent))
        ((x - prin1)) must beDifferent ((up1.root.antecedent ++ up2.root.antecedent - aux1 - aux2))
      }
    }

    "work for ImpRightRule" in {
      val a = ImpRightRule(a2, f2, f2)
      val (up1,  SequentOccurrence(x,y), aux1, aux2, prin1) = ImpRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Imp(f2,f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x) must notContain(aux1)
        (y) must notContain(aux2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux2).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent  - aux2))
        ((x)) must beDifferent ((up1.root.antecedent - aux1))
      }
    }

    "work for NegRightRule" in {
      val a = NegRightRule(a2, f2)
      val (up1,  SequentOccurrence(x,y), aux1, prin1) = NegRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Neg(f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x) must notContain(aux1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent))
        ((x)) must beDifferent ((up1.root.antecedent - aux1))
      }
    }

    "work for NegLeftRule" in {
      val a = NegLeftRule(a2, f2)
      val (up1, SequentOccurrence(x,y), aux1, prin1) = NegLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (Neg(f2))
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y) must notContain(aux1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1).toList.map(x => x.formula))
      }
      "- Formula occurrences in context must be different (if not empty)" in {
        (x - prin1) must beDifferent ((up1.root.antecedent))
        ((y)) must beDifferent ((up1.root.succedent - aux1))
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
      val ax = Axiom( Sequent( aux::Nil, Nil ) )
      val rule = ForallLeftRule(ax, aux, main, subst)
      val (up1,  SequentOccurrence(ant,succ), aux1, prin1) = ForallLeftRule.unapply(rule).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (main)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (ant) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (ant) must notContain(aux1)
      }
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
      val ax = Axiom( Sequent( Nil, aux::Nil ) )
      val rule = ForallRightRule(ax, aux, main, x)
      val (up1,  SequentOccurrence(ant,succ), aux1, prin1) = ForallRightRule.unapply(rule).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (main)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (succ) must contain(prin1)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (succ) must notContain(aux1)
      }
    }

    "A, A, B :- C, D, C should multiset-equal A, B, A :- D, C, C" in {
      Sequent(HOLVarFormula("A")::HOLVarFormula("A")::HOLVarFormula("B")::Nil,
              HOLVarFormula("C")::HOLVarFormula("D")::HOLVarFormula("C")::Nil) must beMultisetEqual(
      Sequent(HOLVarFormula("A")::HOLVarFormula("B")::HOLVarFormula("A")::Nil,
              HOLVarFormula("D")::HOLVarFormula("C")::HOLVarFormula("C")::Nil))
    }
  }
}
