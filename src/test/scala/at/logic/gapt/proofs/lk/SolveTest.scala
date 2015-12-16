package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr.{ StringSymbol, _ }
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.{ HOLSequent, Sequent, SequentMatchers }
import org.specs2.mutable._

class SolveTest extends Specification with SequentMatchers {
  "SolveTest" should {
    "prove sequent where quantifier order matters" in {
      // example from Chaudhuri et.al.: A multi-focused proof system ...
      val List( x, y, u, v ) = List( "x", "y", "u", "v" ) map ( x => Var( StringSymbol( x ), Ti ) )
      val c = Const( StringSymbol( "c" ), Ti )
      val d = Const( StringSymbol( "d" ), Ti -> To )

      val formula = Ex( x, Or( Neg( HOLAtom( d, x :: Nil ) ), All( y, HOLAtom( d, y :: Nil ) ) ) ) // exists x (-d(x) or forall y d(y))

      val inst1 = ETOr(
        ETNeg( ETAtom( HOLAtom( d, u :: Nil ) ) ), // -d(u)
        ETStrongQuantifier( All( y, HOLAtom( d, y :: Nil ) ), v, ETAtom( HOLAtom( d, v :: Nil ) ) ) // forall y d(y) +^v d(v)
      )

      val inst2 = ETOr(
        ETNeg( ETAtom( HOLAtom( d, c :: Nil ) ) ), // -d(c)
        ETStrongQuantifier( All( y, HOLAtom( d, y :: Nil ) ), u, ETAtom( HOLAtom( d, u :: Nil ) ) ) // forall y d(y) +^u d(u)
      )

      // here, the second tree, containing c, must be expanded before u, as u is used as eigenvar in the c branch
      val et = ETWeakQuantifier.applyWithoutMerge( formula, List( ( inst1, u ), ( inst2, c ) ) )
      val etSeq = Sequent() :+ et

      val Some( lkProof ) = solve.expansionProofToLKProof( toShallow( etSeq ), etSeq )
      lkProof.endSequent must beMultiSetEqual( toShallow( etSeq ) )
    }

    "prove top" in { solve.solvePropositional( Sequent() :+ Top() ) must beSome }
    "not prove bottom" in { solve.solvePropositional( Sequent() :+ Bottom() ) must beNone }
    "not refute top" in { solve.solvePropositional( Top() +: Sequent() ) must beNone }
    "refute bottom" in { solve.solvePropositional( Bottom() +: Sequent() ) must beSome }

    "prove ( p ∨ p ) ⊃ ( p ∧ p )" in {
      val p = FOLAtom( "p" )
      val F = ( p | p ) --> ( p & p )
      solve.solvePropositional( Sequent() :+ F ) must beSome
    }

    "prove ( p ∧ p ) ⊃ ( p ∨ p )" in {
      val p = FOLAtom( "p" )
      val F = ( p & p ) --> ( p | p )
      solve.solvePropositional( Sequent() :+ F ) must beSome
    }

    "prove BussTautology(2)" in { solve.solvePropositional( BussTautology( 2 ) ) must beSome }
  }

  "ExpansionProofToLK" should {
    "top" in { ExpansionProofToLK( Sequent() :+ ETTop ) must_== TopAxiom }
    "bottom" in { ExpansionProofToLK( ETBottom +: Sequent() ) must_== BottomAxiom }
  }
}

