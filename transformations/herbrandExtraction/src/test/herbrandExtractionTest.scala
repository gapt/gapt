/*
 * Tests for the extraction of herbrand sequents
 *
 * ATTENTION: herbrandExtraction returns a FSequent
 */

package at.logic.transformations.herbrandSequent

import org.specs._
import org.specs.runner._
import at.logic.language.hol._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import herbrandExtraction._

class herbrandExtractionTest extends SpecificationWithJUnit {

  "The herbrand extraction" should {

    "return the sequent itself for axioms" in {
      val a = HOLVar("a", i->o)
      val x = HOLVar("x", i)
      val ax = HOLAppFormula(a, x)
      val axm = Axiom(ax::Nil, ax::Nil)
      val (hs, terms) = herbrandExtraction(axm)

      (hs) must beEqual (axm.root.toFSequent)
    }

    "skip weak quantifier rules" in {
      "- forall left" in {
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
        val (hs, terms) = herbrandExtraction(rule)

        (hs) must beEqual (ax.root.toFSequent)
      }
      "- exists right" in {
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
        val main = ExVar( z, Or( pz, za ) )    // exists lambda z. p(z) or z(a)
        val ax = Axiom(Nil, aux::Nil)
        val rule = ExistsRightRule(ax, aux, main, subst)
        val (hs, terms) = herbrandExtraction(rule)

        (hs) must beEqual (ax.root.toFSequent)
      }
    }

    // Tests for contraction with quantifications (creating herbrand
    // arrays). Also testing the array expansion.
    "create herbrand arrays for contractions in different instances" in {
      "in contraction left" in {
        val p = HOLVar("p", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val q = HOLVar("q", i -> o)
        val x = HOLVar("x", i)
        val px = HOLAppFormula(p, x) // p(x)
        val pa = HOLAppFormula(p, a) // p(a)
        val pb = HOLAppFormula(p, b) // p(b)
        val qa = HOLAppFormula(q, a) // q(a)
        val substa = a // x -> a
        val substb = b // x -> b
        val all_px = AllVar(x, px) // forall x. p(x)

        val axm1 = Axiom(pa::Nil, pa::Nil)
        val axm2 = Axiom(pb::Nil, pb::Nil)
        val all1 = ForallLeftRule(axm1, pa, all_px, substa)
        val all2 = ForallLeftRule(axm2, pb, all_px, substb)
        val andrght = AndRightRule(all1, all2, pa, pb)
        val contr = ContractionLeftRule(andrght, all_px)
        val andlft = AndLeft1Rule(contr, all_px, qa)

        val (hs, terms) = herbrandExtraction(andlft)

        val expected = new FSequent(And(pa, qa)::And(pb, qa)::Nil, And(pa, pb)::Nil)

        (hs) must beEqual (expected)
      }
      "and in contraction right" in {
        val p = HOLVar("p", i -> o)
        val a = HOLVar("a", i)
        val b = HOLVar("b", i)
        val q = HOLVar("q", i -> o)
        val x = HOLVar("x", i)
        val px = HOLAppFormula(p, x) // p(x)
        val pa = HOLAppFormula(p, a) // p(a)
        val pb = HOLAppFormula(p, b) // p(b)
        val qa = HOLAppFormula(q, a) // q(a)
        val substa = a // x -> a
        val substb = b // x -> b
        val ex_px = ExVar(x, px) // exists x. p(x)

        val axm1 = Axiom(pa::Nil, pa::Nil)
        val axm2 = Axiom(pb::Nil, pb::Nil)
        val exists1 = ExistsRightRule(axm1, pa, ex_px, substa)
        val exists2 = ExistsRightRule(axm2, pb, ex_px, substb)
        val orlft = OrLeftRule(exists1, exists2, pa, pb)
        val contr = ContractionRightRule(orlft, ex_px)
        val orrght = OrRight1Rule(contr, ex_px, qa)

        val (hs, terms) = herbrandExtraction(orrght)

        val expected = new FSequent(Or(pa, pb)::Nil, Or(pa, qa)::Or(pb, qa)::Nil)

        (hs) must beEqual (expected)
      }
    }
  }
}
