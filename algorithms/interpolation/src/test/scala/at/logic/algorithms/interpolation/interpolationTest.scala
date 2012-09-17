
package at.logic.algorithms.interpolation

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable._

import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.propositionalRules._


@RunWith(classOf[JUnitRunner])
class interpolationTest extends SpecificationWithJUnit {
  "interpolation" should {

    "correctly interpolate an axiom with top" in {
      val p = HOLConstFormula(new ConstantStringSymbol("p"))
      val ax = Axiom( p::Nil, p::Nil )
      val npart = Set[FormulaOccurrence]()
      val ppart = Set( ax.root.antecedent(0), ax.root.succedent(0) )
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      ipl must beEqualTo( TopC )
    }

    "correctly create an interpolating proof" in {
      val p = HOLConstFormula(new ConstantStringSymbol("p"))
      val ax = Axiom( p::Nil, p::Nil )
      val npart = Set( ax.root.antecedent(0), ax.root.succedent(0) )
      val ppart = Set[FormulaOccurrence]()
      val ( nproof, pproof, ipl ) = Interpolate( ax, npart, ppart )
      ipl must beEqualTo( BottomC )
      // TODO: nproof.root must beEqualTo p |- p, bot as sequent (not with focc)
    }

    "correctly interpolate a single unary inference with not p" in {
      val p = HOLConstFormula(new ConstantStringSymbol("p"))
      val q = HOLConstFormula(new ConstantStringSymbol("q"))
      val ax = Axiom( p::Nil, p::Nil )
      val pr = OrRight1Rule( ax, p, q )
      val npart = Set( pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.antecedent( 0 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )
      ipl must beEqualTo( Neg( p ) )
    }

    "correctly interpolate a single binary inference with bot or q" in {
      val p = HOLConstFormula(new ConstantStringSymbol("p"))
      val q = HOLConstFormula(new ConstantStringSymbol("q"))
      val axp = Axiom( p::Nil, p::Nil )
      val axq = Axiom( q::Nil, q::Nil )
      val pr = OrLeftRule( axp, axq, p, q )
      val npart = Set( pr.root.antecedent( 0 ), pr.root.succedent( 0 ) )
      val ppart = Set( pr.root.succedent( 1 ) )
      val ( nproof, pproof, ipl ) = Interpolate( pr, npart, ppart )
      ipl must beEqualTo( Or( BottomC, q ) )
    }

  }
}

