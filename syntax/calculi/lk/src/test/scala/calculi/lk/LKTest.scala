/*
 * LKTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import at.logic.language.lambda.substitutions.Substitution
import org.specs._
import org.specs.runner._

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._
import propositionalRules._
import base._
import at.logic.calculi.occurrences.PositionsFOFactory
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

  // implicits for using positions as occurrences
  import at.logic.calculi.occurrences.positions._

  val c1 = HOLVar("a", i->o)
  val v1 = HOLVar("x", i)
  val f1 = HOLAppFormula(c1,v1)
  val ax = Axiom(Sequent(f1::Nil, f1::Nil))
  val a1 = ax // Axiom return a pair of the proof and a mapping and we want only the proof here
  val c2 = HOLVar("b", i->o)
  val v2 = HOLVar("c", i)
  val f2 = HOLAppFormula(c1,v1)
  val f3 = HOLVarFormula("e")
  val a2 = Axiom(Sequent(f2::f3::Nil, f2::f3::Nil))
  val a3 = Axiom(Sequent(f2::f2::f3::Nil, f2::f2::f3::Nil))
  val ap = Axiom(Sequent(f1::f1::Nil, Nil))
  val a4 = ap

  "The factory createDefault" should {
    "works correctly for Axioms" in {
      val myax = Axiom.createDefault(Sequent(f1::f1::Nil, Nil))
      "- Same formulas on the same side must become different occurrences" in {
        val ant = myax.root.antecedent.toList
        (ant.length) must beEqual(2)
        (ant.head) must notBe(ant.last)
      }
      "- FormulaOccurrence mapping must be correct" in {
        val map = myax._2._1
        (map.head) must notBe(map.last)
        (map.filter( o => o != map.head ) ).length must beEqual(1)
      }
    }
    "Works correctly for WweakeningLeft" in {
      val a = WeakeningLeftRule.createDefault(Axiom.createDefault(Sequent(f2::f3::Nil, f2::f3::Nil)), f1)
      val (up1, SequentOccurrence(x,y), prin1) = WeakeningLeftRule.unapply(a).get
      "- Formula occurrences in context must be different (if not empty)" in {
        (x - prin1) must beDifferent ((up1.root.antecedent))
        ((y)) must beDifferent ((up1.root.succedent))
      }
    }
    "Works correctly for WweakeningRight" in {
      val a = WeakeningLeftRule.createDefault(Axiom.createDefault(Sequent(f2::f3::Nil, f2::f3::Nil)), f1)
      val (up1, SequentOccurrence(x,y), prin1) = WeakeningLeftRule.unapply(a).get
      "- Formula occurrences in context must be different (if not empty)" in {
        (y - prin1) must beDifferent ((up1.root.succedent))
        ((x)) must beDifferent ((up1.root.antecedent))
      }
    }
  }
  "The factories/extractors for LK" should {

    "work for Axioms" in {
      "- Formula occurrences have correct formulas" in {
        (a1) must beLike {case Axiom(SequentOccurrence(x,y)) => (x.toArray.apply(0).formula == f1) && (y.toArray.apply(0).formula == f1)}
      }
      "- Same formulas on the same side must become different occurrences" in {
        val ant = a4.root.antecedent.toList
        (ant.length) must beEqual(2)
        (ant.head) must notBe(ant.last)
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
      "- Formula occurrences in context must be the same (if not empty)" in {
        (x - prin1) must beEqual ((up1.root.antecedent))
        ((y)) must beEqual ((up1.root.succedent))
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
      "- Formula occurrences in context must be the same (if not empty)" in {
        (y - prin1) must beEqual ((up1.root.succedent))
        ((x)) must beEqual ((up1.root.antecedent))
      }
    }

    "work for ContractionLeftRule" in {
      val a = ContractionLeftRule(a3, f2)
      val (up1,  SequentOccurrence(x,y), aux1, aux2, prin1) = ContractionLeftRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (f2)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (x.map(x => x.formula)) must contain(prin1.formula)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (x.map(x => x.formula).filter(y => y == aux1.formula)) must beDifferent(2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1 - aux2).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
      }
    }

    "work for ContractionRightRule" in {
      val a = ContractionRightRule(a3, f2)
      val (up1,  SequentOccurrence(x,y), aux1, aux2, prin1) = ContractionRightRule.unapply(a).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (f2)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (y.map(x => x.formula)) must contain(prin1.formula)
      }
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.map(y => y.formula).filter(x => x == aux1.formula)) must beDifferent(2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1 - aux2).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
      }
    }

    "work for CutRule" in {
      val a = CutRule(a2, a3, f2)
      val (up1, up2, SequentOccurrence(x,y), aux1, aux2) = CutRule.unapply(a).get
      "- Lower sequent must not contain the auxiliary formulas" in {
        (y.filter(z => z.formula == f2)).size must beEqual(2)
        (x.filter(z => z.formula == f2)).size must beEqual(2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y).map(x => x.formula)) must beEqual (((up1.root.succedent - aux1) ++ up2.root.succedent).map(x => x.formula))
        ((x).map(x => x.formula)) must beEqual ((up1.root.antecedent ++ (up2.root.antecedent - aux2)).map(x => x.formula))
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
        (y.map(z => z.formula)) must notContain(f1)
        (y.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (x.toList.map(x => x.formula)) must beEqual ((up1.root.antecedent.toList ++ up2.root.antecedent.toList).map(x => x.formula))
        ((y.toList.map(x => x.formula).filterNot(x => x == And(f1,f2)))) must beEqual (((up1.root.succedent - aux1).toList ++ (up2.root.succedent  - aux2).toList).map(x => x.formula))
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
        (x.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
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
        (x.map(z => z.formula)) must notContain(f1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
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
        (x.map(z => z.formula)) must notContain(f1)
        (x.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (y.toList.map(x => x.formula)) must beEqual ((up1.root.succedent.toList ++ up2.root.succedent.toList).map(x => x.formula))
        ((x - prin1).toList.map(x => x.formula)) must beEqual (((up1.root.antecedent - aux1).toList ++ (up2.root.antecedent  - aux2).toList).map(x => x.formula))
      }
      "- Descendants must be correctly computed" in {
        "(1)" in {
          // get descendant of occurrence of left auxiliary formula
          a.getDescendantInLowerSequent(a1.root.antecedent.find(_ == 1).get) must beLike {
            case Some(x) => x.formula == Or(f1, f2)
            case None => false
          }
        }
        "(2)" in {
          // get descendant of occurrence of left premise context in succedent
          a.getDescendantInLowerSequent(a1.root.succedent.find(_ == 1).get) must beLike {
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
        (y.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
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
        (y.map(z => z.formula)) must notContain(f1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
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
        (y.filter(z => z.formula == f1)).size must beEqual(1)
        (x.filter(z => z.formula == f2)).size must beEqual(1)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        (y.toList.map(x => x.formula)) must beEqual ((up1.root.succedent.toList ++ (up2.root.succedent - aux1).toList).map(x => x.formula))
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent.toList ++ (up2.root.antecedent - aux2).toList).map(x => x.formula))
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
        (x.map(z => z.formula)) must notContain(f2)
        (y.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux2).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
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
        (x.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((y - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.succedent).toList.map(x => x.formula))
        ((x).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent - aux1).toList.map(x => x.formula))
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
        (y.map(z => z.formula)) must notContain(f2)
      }
      "- Context should stay unchanged with regard to multiset equality" in {
        ((x - prin1).toList.map(x => x.formula)) must beEqual ((up1.root.antecedent).toList.map(x => x.formula))
        ((y).toList.map(x => x.formula)) must beEqual ((up1.root.succedent - aux1).toList.map(x => x.formula))
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
      val (up1,  SequentOccurrence(ant,succ), aux1, prin1, term) = ForallLeftRule.unapply(rule).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (main)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (ant) must contain(prin1)
      }
      /*"- Lower sequent must not contain the auxiliary formulas" in {
        (ant) must notContain(aux1)
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
      val ax = Axiom( Sequent( Nil, aux::Nil ) )
      val rule = ForallRightRule(ax, aux, main, x)
      val (up1,  SequentOccurrence(ant,succ), aux1, prin1, ev) = ForallRightRule.unapply(rule).get
      "- Principal formula is created correctly" in {
        (prin1.formula) must beEqual (main)
      }
      "- Principal formula must be contained in the right part of the sequent" in {
        (succ) must contain(prin1)
      }
      /*"- Lower sequent must not contain the auxiliary formulas" in {
        (succ) must notContain(aux1)
      } */
    }

    "A, A, B :- C, D, C should multiset-equal A, B, A :- D, C, C" in {
      Sequent(HOLVarFormula("A")::HOLVarFormula("A")::HOLVarFormula("B")::Nil,
              HOLVarFormula("C")::HOLVarFormula("D")::HOLVarFormula("C")::Nil) must beMultisetEqual(
      Sequent(HOLVarFormula("A")::HOLVarFormula("B")::HOLVarFormula("A")::Nil,
              HOLVarFormula("D")::HOLVarFormula("C")::HOLVarFormula("C")::Nil))
    }
  }
  "Equals" should {
    "denote multiset equals" in {
      "1" in {
        Sequent(f2::f3::f2::Nil, f3::f2::f2::Nil) must beEqual (Sequent(f2::f2::f3::Nil, f2::f2::f3::Nil))
      }
    }
    "fail to denote set equals" in {
      "1" in {
        Sequent(f2::f3::f3::Nil, f3::f2::f2::Nil) mustNot beEqual (Sequent(f2::f2::f3::Nil, f2::f2::f3::Nil))
      }
    }
  }

  def skolem_symbol_stream_from(n: Int): Stream[ConstantStringSymbol] =
    Stream.cons(ConstantStringSymbol( "s_" + n ), skolem_symbol_stream_from( n + 1 ) )

  def skolem_symbol_stream = skolem_symbol_stream_from( 0 )

  def even[A]( s: Stream[A] ) : Stream[A] = if (s.isEmpty) Stream.Empty else
    Stream.cons( s.head, even(s.tail.tail) )

  def odd[A]( s: Stream[A] ) : Stream[A] = if (s.isEmpty) Stream.Empty
    else if (s.tail.isEmpty) Stream.Empty
    else Stream.cons( s.tail.head, odd(s.tail.tail) )

  def invert( pol: Int ) =
    if (pol == 0)
      1
    else
      0

  def sk(f: HOLFormula, pol: Int, terms: List[HOLExpression], symbols: Stream[ConstantStringSymbol]) : HOLFormula = f match {
    case And(l, r) => And( sk( l , pol, terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Or(l, r) => Or( sk( l , pol, terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Imp(l, r) => Imp( sk( l , invert( pol ), terms, even( symbols ) ), sk( r, pol, terms, odd( symbols ) ) )
    case Neg(f) => Neg( sk( f, invert( pol ), terms, symbols ) )
    case ExVar(x, f) =>
      if (pol == 1)
      {
        println( "skolemizing ExQ")
        val sub = Substitution(x, Function( symbols.head, terms, x.exptype ) )
        println( "substitution: " + sub )
        println( "before: " + f )
        println( "after: " + sub( f ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        ExVar(x, sk( f, pol, terms :+ x.asInstanceOf[HOLVar], symbols ) )
    case AllVar(x, f) =>
      if (pol == 0)
      {
        //println( "skolemizing AllQ")
        val sub = Substitution(x, Function( symbols.head, terms, x.exptype ) )
        //println( "substitution: " + sub )
        //println( f )
        //println( sub( f ) )
        // TODO: should not be necessary to cast here, Formula is closed under substitution
        val res = sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
        //println( "result of skolemization: " + res )
        res
      }
      else // TODO: should not be necessary to cast! try to change it in hol.scala.
        AllVar(x, sk( f, pol, terms :+ x.asInstanceOf[HOLVar], symbols ) )
    case Atom(_,_) => f
  }

  /*"A complex test for checking substitution in quantifiers" should {
    "simulate skolemization" in {


      val x = HOLVar("x", i)
      val y = HOLVar("y", i)
      val f = AllVar( x, Atom("P", x::Nil ) )
      val s0 = new ConstantStringSymbol( "s_0" )
      val s1 = new ConstantStringSymbol( "s_1" )
      val s2 = new ConstantStringSymbol( "s_2" )
      val s3 = new ConstantStringSymbol( "s_3" )
      val a = HOLVar("a", i)
      val b = HOLVar("b", i)
      val Rab = Atom( "R", a::b::Nil )
      val exyRay = ExVar( y, Atom( "R", a::y::Nil ) )
      val allxexyRxy = AllVar( x, ExVar( y, Atom( "R", x::y::Nil ) ) )
      //sk(allxexyRxy, 1, Nil, skolem_symbol_stream)
      val exyRsy = Substitution
      //sk(exyRay, 1, new HOLConst(skolem_symbol_stream.head, i)::Nil, skolem_symbol_stream.tail)

      exyRay match { case ExVar(x, f) => {
      println( "skolemizing ExQ")
      val sub = Substitution(x, Function( skolem_symbol_stream.tail.head, new HOLConst(skolem_symbol_stream.head, i)::Nil, x.exptype ) )
      println( "substitution: " + sub )
      println( "before: " + f )
      println( "after: " + sub( f ) )
      // TODO: should not be necessary to cast here, Formula is closed under substitution
      sk( sub( f ).asInstanceOf[HOLFormula], pol, terms, symbols.tail )
      }}

      //val ax = Axiom( Sequent( Rab::Nil, Rab::Nil ) )
      //val r1 = ExistsRightRule( ax._1, Rab, exyRay, b )
      //val r2 = ExistsLeftRule( r1, Rab, exyRay, b )
      //val r3 = ForallLeftRule( r2, exyRay, allxexyRxy, a )
      //val proof = ForallRightRule( r3, exyRay, allxexyRxy, a )

      //val fs0 = HOLConst( s0, i -> i )
      //val cs1 = HOLConst( s1, i )
      //val s0s1 = HOLApp( fs0, cs1 )
      //val sR = Atom( "R", cs1::s0s1::Nil )
      //val sax = Axiom( Sequent( sR::Nil, sR::Nil ) )
      //val exyRs1y = ExVar( y, Atom( "R", cs1::y::Nil ) )
      //val allxRxs0x = AllVar( x, Atom( "R", x::HOLApp( fs0, x )::Nil ) )

      //val sr1 = ExistsRightRule( sax._1, sR, exyRs1y, s0s1 )
      //val proof_sk = ForallLeftRule( sr1, sR, allxRxs0x, cs1 )

      sk()
    }
  }*/
}
