package gapt.proofs.lk

import gapt.expr._
import gapt.examples.tip.isaplanner.{ prop_08, prop_15, prop_59 }
import gapt.expr.Substitution
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.InductiveType
import gapt.proofs.{ Sequent, SequentMatchers }
import gapt.proofs.gaptic.{ Lemma, ProofState, allR, cut, escargot, induction, insert, refl, rewrite }
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.transformations.inductionNormalForm
import gapt.proofs.lk.util.instanceProof
import gapt.proofs.lk.util.isInductionFree
import gapt.proofs.lk.util.regularize
import org.specs2.mutable.Specification

class InductionEliminationTests extends Specification with SequentMatchers {

  "isaplanner prop_08: induction should be eliminated" in {
    implicit val ctx = prop_08.ctx
    val proof = regularize( prop_08.proof1 )
    val term_n = le"S(S(S(Z)))"
    val term_m = le"S(S(S(S(S(Z)))))"
    val term_k = le"S(S(S(S(S(S(S(Z)))))))"
    val instProof = instanceProof( proof, term_n :: term_m :: term_k :: Nil )
    val inductionFreeProof = inductionNormalForm( instProof )
    isInductionFree( inductionFreeProof ) must_== true
    instProof.conclusion must beSetEqual( inductionFreeProof.conclusion )
  }

  "isaplanner prop_15: induction should be eliminated" in {
    implicit val ctx = prop_15.ctx
    val proof = regularize( prop_15.proof.subProofAt( 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: Nil ) )
    val term_x = le"S(S(S(S(S(S(S(Z)))))))"
    val term_xs = le"cons(S(S(S(Z))), cons(S(S(S(S(S(Z))))),nil))"
    val sigma1Proof = Substitution( hov"x:Nat" -> term_x, hov"xs:list" -> term_xs )( proof )
    val inductionFreeProof = inductionNormalForm( sigma1Proof )
    isInductionFree( inductionFreeProof ) must_== true
    sigma1Proof.conclusion must beSetEqual( inductionFreeProof.conclusion )
  }

  "all inductions should be eliminated" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    ctx += hoc"'+': nat>nat>nat"
    ctx += Notation.Infix( "+", Precedence.plusMinus )

    val axioms = Seq(
      "ap1" -> hof"∀y 0+y = y",
      "ap2" -> hof"∀x∀y s(x)+y = s(x+y)" )

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

    val term_x = le"s(0)"
    val term_y = le"s(0)"

    val sigma1Proof = Substitution( hov"x:nat" -> term_x, hov"y:nat" -> term_y )(
      proof.subProofAt( 0 :: 0 :: Nil ) )
    val inductionFreeProof = inductionNormalForm( sigma1Proof )
    isInductionFree( inductionFreeProof ) must_== true
    sigma1Proof.conclusion must beSetEqual( inductionFreeProof.conclusion )
  }

  "several unfolding steps are required" in {
    implicit val ctx = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    ctx += hoc"'+': nat>nat>nat"
    ctx += Notation.Infix( "+", Precedence.plusMinus )

    val axioms = Seq(
      "ap1" -> hof"∀y 0+y = y",
      "ap2" -> hof"∀x∀y s(x)+y = s(x+y)" )

    val lemma_2 = hof"!x !y x + s(y) = s(x) + y"
    val lemma_2_proof = Lemma( axioms ++: Sequent() :+ ( "goal" -> lemma_2 ) ) {
      allR
      induction( hov"x:nat" )
      allR
      rewrite ltr "ap2" in "goal"
      rewrite.many ltr "ap1" in "goal"
      refl
      allR
      rewrite ltr "ap2" in "goal"
      rewrite ltr "IHx_0" in "goal"
      rewrite rtl "ap2" in "goal"
      refl
    }

    val lemma_1 = hof"!x x + 0 = x"
    var lemma_1_state = ProofState( axioms ++: Sequent() :+ ( "goal" -> lemma_1 ) )
    lemma_1_state += allR
    lemma_1_state += cut( "1", lemma_2 ) andThen insert( lemma_2_proof )
    lemma_1_state += cut( "2", lemma_2 ) andThen insert( lemma_2_proof )
    lemma_1_state += cut( "3", lemma_2 ) andThen insert( lemma_2_proof )
    lemma_1_state += induction( hov"x:nat", "goal" )
    lemma_1_state += rewrite ltr "ap1" in "goal"
    lemma_1_state += refl
    lemma_1_state += rewrite ltr "ap2" in "goal"
    lemma_1_state += rewrite ltr "IHx_0" in "goal"
    lemma_1_state += refl
    val lemma_1_proof = lemma_1_state.partialProof

    var proof_state = ProofState( axioms ++: Sequent() :+ ( "goal" -> hof"!x !y x + y = y + x" ) )
    proof_state += allR
    proof_state += allR
    proof_state += induction( hov"x:nat" )
    proof_state += rewrite ltr "ap1" in "goal"
    proof_state += cut( "l1", lemma_1 ) andThen insert( lemma_1_proof )
    proof_state += rewrite ltr "l1" in "goal"
    proof_state += refl
    proof_state += cut( "l1", lemma_1 ) andThen insert( lemma_1_proof )
    proof_state += cut( "l2", lemma_2 ) andThen insert( lemma_2_proof )
    proof_state += rewrite ltr "l2" in "goal"
    proof_state += rewrite.many ltr "ap2" in "goal"
    proof_state += rewrite ltr "IHx_0" in "goal"
    proof_state += refl

    val proof = proof_state.partialProof

    val term_x = le"s(0)"
    val term_y = le"s(0)"

    val sigma1Proof = Substitution( hov"x:nat" -> term_x, hov"y:nat" -> term_y )(
      proof.subProofAt( 0 :: 0 :: Nil ) )
    val inductionFreeProof = inductionNormalForm( sigma1Proof )

    isInductionFree( inductionFreeProof ) must_== true
  }

  "induction elimination isaplanner prop_59" in {
    implicit val ctx = prop_59.ctx
    val inductiveProof = prop_59.proof_1
    val instProof = instanceProof( inductiveProof, le"nil" :: le"nil" :: Nil )
    val indFreeProof = inductionNormalForm( instProof )
    indFreeProof.conclusion must beMultiSetEqual( instProof.conclusion )
    isInductionFree( indFreeProof ) must_== true
  }

  "issue #699" in {
    import gapt.examples
    implicit val ctx = examples.theories.nat.ctx
    val p = instanceProof(
      examples.theories.nat.addcomm.combined(),
      Seq( le"s (s 0 : nat)", le"0 : nat" ) )
    isInductionFree( inductionNormalForm( p ) ) must_== true
  }
}
