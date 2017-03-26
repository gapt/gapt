package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.examples.tip.isaplanner.{ prop_08, prop_15 }
import at.logic.gapt.expr.Substitution
import at.logic.gapt.proofs.{ Context, Sequent, SequentMatchers }
import at.logic.gapt.proofs.gaptic.{ Lemma, allR, cut, escargot, induction, refl, rewrite }
import org.specs2.mutable.Specification

class InductionEliminationTests extends Specification with SequentMatchers {

  private def isCutFree( proof: LKProof ): Boolean =
    !proof.subProofs.exists( subProof => subProof match {
      case CutRule( _, _, _, _ ) => true
      case _                     => false
    } )

  private def isInductionFree( proof: LKProof ): Boolean =
    !proof.subProofs.exists( subProof => subProof match {
      case InductionRule( _, _, _ ) => true
      case _                        => false
    } )

  "induction should be unfolded and cuts should be eliminated" in {
    implicit val ctx = prop_08.ctx
    val proof = regularize( prop_08.proof1 )
    val term_n = le"S(S(S(Z)))"
    val term_m = le"S(S(S(S(S(Z)))))"
    val term_k = le"S(S(S(S(S(S(S(Z)))))))"
    val sigma1Proof = LKProofSubstitutableDefault.applySubstitution(
      new Substitution( Map( hov"n:Nat" -> term_n, hov"m:Nat" -> term_m, hov"k:Nat" -> term_k ) ),
      proof
    )
    val inductionFree = ReductiveCutElimination.eliminateInduction( sigma1Proof )
    if ( !isInductionFree( inductionFree ) || !isCutFree( inductionFree ) ) {
      failure
    }
    sigma1Proof.conclusion must beSetEqual( inductionFree.conclusion )
  }

  "induction should be eliminated" in {
    implicit val ctx = prop_15.ctx
    val proof = regularize( prop_15.proof.subProofAt( 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: Nil ) )
    val term_x = le"S(S(S(S(S(S(S(Z)))))))"
    val term_xs = le"cons(S(S(S(Z))), cons(S(S(S(S(S(Z))))),nil))"
    val sigma1Proof = LKProofSubstitutableDefault.applySubstitution(
      new Substitution( Map( hov"x:Nat" -> term_x, hov"xs:list" -> term_xs ) ),
      proof
    )
    val inductionFree = ReductiveCutElimination.eliminateInduction( sigma1Proof )
    if ( !isInductionFree( inductionFree ) ) {
      failure
    }
    sigma1Proof.conclusion must beSetEqual( inductionFree.conclusion )
  }

  "all inductions should be eliminated" in {
    implicit var ctx = Context()
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    ctx += hoc"'+': nat>nat>nat"

    val axioms = Seq(
      "ap1" -> hof"∀y 0+y = y",
      "ap2" -> hof"∀x∀y s(x)+y = s(x+y)"
    )

    val proof = Lemma( axioms ++: Sequent() :+ ( "goal" -> hof"!x !y x + y = y + x" ) ) {
      allR; allR;
      induction( hov"x:nat" )
      induction( hov"y:nat" )
      refl
      rewrite ltr "ap2" in "goal"
      rewrite rtl "IHy_0" in "goal"
      rewrite.many ltr "ap1" in "goal"
      refl
      induction( hov"y:nat" )
      rewrite ltr "ap2" in "goal"
      rewrite ltr "ap1" in "goal"
      cut( "cf", hof"x_0 + 0 = x_0" )
      induction( hov"x_0:nat", "cf" )
      rewrite ltr "ap1" in "cf"
      refl
      rewrite ltr "ap2" in "cf"
      rewrite ltr "IHx_0_0" in "cf"
      refl
      rewrite ltr "cf" in "goal"
      refl
      rewrite.many ltr "ap2" in "goal"
      rewrite rtl "IHy_0" in "goal"
      cut( "cf", hof"x_0 + s(y_0) = s(x_0) + y_0" )
      induction( hov"x_0:nat", "cf" )
      escargot
      escargot
      escargot
    }

    val term_x = le"s(s(s(0)))"
    val term_y = le"s(s(s(0)))"

    val sigma1Proof = LKProofSubstitutableDefault.applySubstitution(
      new Substitution( Map( hov"x:nat" -> term_x, hov"y:nat" -> term_y ) ),
      proof.subProofAt( 0 :: 0 :: Nil )
    )
    val inductionFree = ReductiveCutElimination.eliminateInduction( sigma1Proof )
    if ( !isInductionFree( inductionFree ) ) {
      failure
    }
    sigma1Proof.conclusion must beSetEqual( inductionFree.conclusion )
  }
}
