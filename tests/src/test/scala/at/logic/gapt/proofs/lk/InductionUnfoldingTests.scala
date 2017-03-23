package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic.{ ProofState, _ }
import at.logic.gapt.proofs.{ Context, Sequent }
import org.specs2.mutable._

class InductionUnfoldingOnTreesTest extends Specification {

  def containsInduction( proof: LKProof ): Boolean =
    proof.subProofs.exists( _.isInstanceOf[InductionRule] )

  object proofs extends TacticsProof {
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    ctx += Context.InductiveType( "tree", hoc"leaf: tree", hoc"node:tree>tree>nat>tree" )
    ctx += hoc"'+': nat>nat>nat"
    ctx += hoc"mirror: tree>tree"
    ctx += hoc"size: tree>nat"

    val axioms = Seq(
      "ap1" -> hof"∀y 0+y = y",
      "ap2" -> hof"∀x∀y s(x)+y = s(x+y)",
      "as1" -> hof"size(leaf) = 0",
      "as2" -> hof"∀t1 ∀t2 ∀x size(node(t1,t2,x)) = size(t1) + size(t2)",
      "am1" -> hof"mirror(leaf) = leaf",
      "am2" -> hof"∀t1 ∀t2 ∀x mirror(node(t1,t2,x)) = node(mirror(t1),mirror(t2),x)" )

    val goal = hof"size(t) = size(mirror(t))"

    def general_proof_goal: LKProof = {
      var proofState = ProofState( axioms ++: Sequent() :+ "goal" -> goal )
      proofState += induction( hov"t:tree" )
      proofState += escargot
      proofState += escargot
      regularize( proofState.result )
    }

    val testTerm1: Expr = le"node(node(node(leaf, leaf, 0), node(leaf, leaf, s(0)), 0), node(leaf, leaf, s(s(0))), 0)"
    val testTerm2: Expr = le"leaf"

    val inductiveGroundProof1 = Substitution( hov"t:tree" -> testTerm1 )( general_proof_goal )

    val inductiveGroundProof2 = Substitution( hov"t:tree" -> testTerm2 )( general_proof_goal )
  }
  import proofs._

  "unfolding induction for base term" in {
    val inductivePart = inductiveGroundProof2.subProofAt( 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: Nil ).asInstanceOf[InductionRule]
    val inductionFreeProof = unfoldInduction( inductivePart )
    if ( containsInduction( inductionFreeProof ) ) {
      failure( "induction was not eliminated" )
    }
    if ( !inductionFreeProof.endSequent.multiSetEquals( inductivePart.endSequent ) ) {
      failure( "the induction free proof does not prove the same end-sequent" )
    }
    success
  }

  "unfolding induction for complex term" in {
    val inductivePart = inductiveGroundProof1.subProofAt( 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: Nil ).asInstanceOf[InductionRule]
    val inductionFreeProof = unfoldInduction( inductivePart )
    if ( containsInduction( inductionFreeProof ) ) {
      failure( "induction was not eliminated" )
    }
    if ( !inductionFreeProof.endSequent.multiSetEquals( inductivePart.endSequent ) ) {
      failure( "the induction free proof does not prove the same end-sequent" )
    }
    success
  }
}

