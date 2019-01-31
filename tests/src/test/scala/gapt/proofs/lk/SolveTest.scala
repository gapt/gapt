package gapt.proofs.lk

import gapt.examples
import gapt.examples.{ BussTautology, primediv }
import gapt.expr._
import gapt.expr.hol.existentialClosure
import gapt.proofs.expansion._
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.transformations.eliminateDefinitions
import gapt.proofs.{ Sequent, SequentMatchers }
import gapt.provers.escargot.Escargot
import org.specs2.mutable._

class SolveTest extends Specification with SequentMatchers {
  "SolveTest" should {
    "prove sequent where quantifier order matters" in {
      // example from Chaudhuri et.al.: A multi-focused proof system ...
      // here, the second tree, containing c, must be expanded before u, as u is used as eigenvar in the c branch
      val et = ExpansionTree( hof"∃x (¬d(x) ∨ ∀y d(y))", Polarity.InSuccedent,
        ETtWeak(
          le"u" -> ETtBinary( ETtUnary( ETtAtom ), ETtStrong( hov"v", ETtAtom ) ),
          le"c" -> ETtBinary( ETtUnary( ETtAtom ), ETtStrong( hov"u", ETtAtom ) ) ) )
      val etSeq = Sequent() :+ et

      val Right( lkProof ) = ExpansionProofToLK( ExpansionProof( etSeq ) )
      lkProof.endSequent must beMultiSetEqual( etSeq.shallow )
    }

    "prove top" in { solvePropositional( Sequent() :+ Top() ).toOption must beSome }
    "not prove bottom" in { solvePropositional( Sequent() :+ Bottom() ).toOption must beNone }
    "not refute top" in { solvePropositional( Top() +: Sequent() ).toOption must beNone }
    "refute bottom" in { solvePropositional( Bottom() +: Sequent() ).toOption must beSome }

    "prove ( p ∨ p ) → ( p ∧ p )" in {
      val F = hof"p|p -> p&p"
      solvePropositional( F ).toOption must beSome
    }

    "prove ( p ∧ p ) → ( p ∨ p )" in {
      val F = hof"p&p -> p|p"
      solvePropositional( F ).toOption must beSome
    }

    "prove BussTautology(2)" in { solvePropositional( BussTautology( 2 ) ).toOption must beSome }
  }

  "ExpansionProofToLK" should {
    "top" in {
      ExpansionProofToLK( ExpansionProof( Sequent() :+ ETTop( Polarity.InSuccedent ) ) ) must_==
        Right( TopAxiom )
    }
    "bottom" in {
      ExpansionProofToLK( ExpansionProof( ETBottom( Polarity.InAntecedent ) +: Sequent() ) ) must_==
        Right( BottomAxiom )
    }

    "equality" in {
      val Some( expansion ) = Escargot getExpansionProof existentialClosure(
        hof"x+(y+z) = (x+y)+z" +:
          hof"x+y = y+x" +:
          Sequent()
          :+ hof"(a+(b+c))+(d+e) = (c+(d+(a+e)))+b" )
      val Right( lk ) = ExpansionProofToLK( expansion )
      lk.conclusion must beMultiSetEqual( expansion.shallow )
    }

    "cuts" in {
      val es = ETAtom( hoa"p 0", Polarity.InAntecedent ) +:
        ExpansionTree( hof"∀x (p x → p (s x))", Polarity.InAntecedent, ETtWeak(
          le"z" -> ETtBinary( ETtAtom, ETtAtom ),
          le"s z" -> ETtBinary( ETtAtom, ETtAtom ) ) ) +:
        Sequent() :+
        ETAtom( hoa"p (s (s (s (s 0))))", Polarity.InSuccedent )
      val cut = ETCut(
        hof"∀x (p x → p (s (s x)))",
        ETtStrong( hov"z", ETtBinary( ETtAtom, ETtAtom ) ),
        ETtWeak(
          le"0" -> ETtBinary( ETtAtom, ETtAtom ),
          le"s (s 0)" -> ETtBinary( ETtAtom, ETtAtom ) ) )
      val epwc = ExpansionProof( cut +: es )
      ExpansionProofToLK( epwc ) must beLike {
        case Right( p ) => p.conclusion must beMultiSetEqual( epwc.nonCutPart.shallow )
      }
    }

    "read back higher order prime divisor proof" in {
      import primediv._
      val p = eliminateDefinitions( proof )
      ExpansionProofToLK.withTheory.apply( LKToExpansionProof( p ) ) must beLike {
        case Right( p_ ) => p_.conclusion must beMultiSetEqual( p.conclusion )
      }
    }

    "useless quantifiers" in {
      val et = ETWeakQuantifier(
        hof"∃x true",
        Map(
          le"c" -> ETTop( Polarity.InSuccedent ),
          le"d" -> ETTop( Polarity.InSuccedent ) ) )
      ExpansionProofToLK( ExpansionProof( Sequent() :+ et ) ) must beLike {
        case Right( p ) => p.conclusion must_== ( Sequent() :+ et.shallow )
      }
    }

    "skolem quantifiers" in {
      val formula = hof"?x!y p(x,y) -> !y?x p(x,y)"
      val Some( skolemExpansion ) = Escargot getExpansionProof formula
      ExpansionProofToLK( skolemExpansion ) must beLike {
        case Right( p ) => p.conclusion must_== ( Sequent() :+ formula )
      }
    }

    "induction in addcomm" in {
      import examples.theories.nat._
      val example = addcomm.proof
      val exp = LKToExpansionProof( example )
      ExpansionProofToLK( exp ) must beLike {
        case Right( p ) => p.conclusion must beMultiSetEqual( example.conclusion )
      }
    }

    "induction in revmap" in {
      import examples.theories.list._
      val example = revmap.proof
      val exp = LKToExpansionProof( example )
      ExpansionProofToLK( exp ) must beLike {
        case Right( p ) => p.conclusion must beMultiSetEqual( example.conclusion )
      }
    }

  }
}

