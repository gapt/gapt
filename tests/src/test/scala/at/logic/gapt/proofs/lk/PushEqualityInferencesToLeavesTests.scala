package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.Abs
import at.logic.gapt.proofs.{ Ant, Context, Sequent, SequentMatchers, Suc }
import at.logic.gapt.proofs.gaptic.OpenAssumption
import org.specs2.mutable.Specification

class PushEqualityInferencesToLeavesTests extends Specification with SequentMatchers {

  "right equality equation formula introduced by left weakening" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ "" -> hof"A(x)" )
      u ( WeakeningLeftRule( _, hof"x = y" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] )
    reduction must beEqualTo( None )
  }

  "right equality neither equation nor auxiliary formula introduced by left weakening" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"x = y" ) +: Sequent() :+ "" -> hof"A(x)" )
      u ( WeakeningLeftRule( _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[WeakeningLeftRule]
  }

  "right equality auxiliary formula is introduced by right weakening" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"x = y" ) +: Sequent() )
      u ( WeakeningRightRule( _, hof"A(x)" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[WeakeningRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[OpenAssumption]
  }

  "right equality auxiliary formula not introduced by right weakening" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"x = y" ) +: Sequent() :+ ( "" -> hof"A(x)" ) )
      u ( WeakeningRightRule( _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[WeakeningRightRule]
  }

  "right equality equation formula introduced by left contraction" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"x = y" ) +: ( "" -> hof"x = y" ) +: Sequent() :+ ( "" -> hof"A(x)" ) )
      u ( ContractionLeftRule( _, hof"x = y" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "right equality equation formula not introduced by left contraction" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"B" ) +: ( "" -> hof"x = y" ) +: Sequent() :+ ( "" -> hof"A(x)" ) )
      u ( ContractionLeftRule( _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "equality right upper sequent introduced by cut that splits principal formulas" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s = t" ) +: Sequent() :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      b ( CutRule( _, _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "equality right upper sequent introduced by cut that splits principal formulas" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"s = t" ) +: Sequent() )
      b ( CutRule( _, _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "equality right upper sequent introduced by cut that does not split principal formulas (left)" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s = t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: Sequent() )
      b ( CutRule( _, _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[CutRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right rule upper sequent introduced by cut that does not split principal formulas (right)" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"s = t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      b ( CutRule( _, _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[CutRule]
    reduction.subProofAt( 1 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right upper sequent introduced by right negation inf. auxiliary formula is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      u ( NegRightRule( _, Ant( 0 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[NegRightRule]
  }

  "equality right upper sequent intro. by right negation inf. auxiliary formula is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: Sequent() )
      u ( NegRightRule( _, Ant( 1 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"¬A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[NegRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality right upper sequent introduced by and right, eq and aux split (left)" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"C" ) )
      b ( AndRightRule( _, Suc( 1 ), _, Suc( 0 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right upper sequent intro. by and right, eq and aux split (right)" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"C" ) )
      c OpenAssumption( Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) )
      b ( AndRightRule( _, Suc( 0 ), _, Suc( 1 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 1 :: 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro by and right; eq and aux not split" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"C" ) )
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) )
      b ( AndRightRule( _, Suc( 0 ), _, Suc( 1 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[AndRightRule]
    reduction.subProofAt( 1 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by and right; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"A(s)" ) )
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B(s)" ) )
      b ( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"(A(x)&B(x)):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[AndRightRule]
  }

  "equality right; upper sequent intro. by or right; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) :+ ( "" -> hof"C" ) )
      u ( OrRightRule( _, Suc( 1 ), Suc( 2 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[OrRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by or right; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B(s)" ) )
      u ( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"(A(x)∨B(x)):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[OrRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
    reduction.subProofAt( 0 :: 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by imp. right; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"B" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"C" ) )
      u ( ImpRightRule( _, Ant( 1 ), Suc( 1 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ImpRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by imp. right; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: Sequent() :+ ( "" -> hof"B(s)" ) )
      u ( ImpRightRule( _, Ant( 1 ), Suc( 0 ) ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"(A(x)⊃B(x)):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ImpRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
    reduction.subProofAt( 0 :: 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality right; upper sequent intro. by exists right; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B(t)" ) :+ ( "" -> hof"A(s)" ) )
      u ( ExistsRightRule( _, Suc( 0 ), hof"∃x B(x)", le"t" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ExistsRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent introduced by exists right; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s, s)" ) )
      u ( ExistsRightRule( _, Suc( 0 ), hof"∃x A(x, s)", le"s" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"y", le"∃x A(x, y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ExistsRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequnent introduced by forall right; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B(x)" ) )
      u ( ForallRightRule( _, Suc( 1 ), hov"x", hov"x" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ForallRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by forall right; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(x, s)" ) )
      u ( ForallRightRule( _, Suc( 0 ), hov"x", hov"x" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"y", le"∀x A(x, y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ForallRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by right contr.; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B" ) :+ ( "" -> hof"B" ) :+ ( "" -> hof"A(s)" ) )
      u ( ContractionRightRule( _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. by contr. right; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"A(s)" ) )
      u ( ContractionRightRule( _, hof"A(s)" ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent introduced by left negation inf" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"B" ) )
      u ( NegLeftRule( _, hof"B" ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[NegLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro. and left inf." in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"C" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      u ( AndLeftRule( _, hof"B & C" ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[AndLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent intro by or left inf." in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"C" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      b ( OrLeftRule( _, Ant( 0 ), _, Ant( 0 ) ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[OrLeftRule]
  }

  "equality right; upper sequent intro left imp. inf." in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"A(s)" ) :+ ( "" -> hof"C" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      b ( ImpLeftRule( _, Suc( 1 ), _, Ant( 0 ) ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[ImpLeftRule]
  }

  "equality right; upper sequent intro. by forall left inf." in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"B(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      u ( ForallLeftRule( _, Ant( 0 ), hof"!x B(x)", le"s" ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ForallLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality right; upper sequent introduced by exists left inf." in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"B(x)" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      u ( ExistsLeftRule( _, Ant( 0 ), hof"?x B(x)", hov"x:i" ) )
      u ( EqualityRightRule( _, Ant( 1 ), Suc( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ExistsLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality left; upper sequent intro. by weakening left; eq is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: Sequent() )
      u ( WeakeningLeftRule( _, hof"s=t" ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ) must beEmpty
  }

  "equality left; upper sequent intro. by weakening left; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() )
      u ( WeakeningLeftRule( _, hof"A(s)" ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion.multiSetEquals( proof.conclusion )
    reduction must beAnInstanceOf[WeakeningLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[OpenAssumption]
  }

  "equality left; upper sequent intro. by weakening left; neither eq nor aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      u ( WeakeningLeftRule( _, hof"B" ) )
      u ( EqualityLeftRule( _, Ant( 2 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[WeakeningLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by weakenig right;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      u ( WeakeningRightRule( _, hof"B" ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[WeakeningRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by contraction left; eq is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      u ( ContractionLeftRule( _, Ant( 1 ), Ant( 2 ) ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by contraction left; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      u ( ContractionLeftRule( _, Ant( 0 ), Ant( 1 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by contraction right;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B" ) :+ ( "" -> hof"B" ) )
      u ( ContractionRightRule( _, Suc( 0 ), Suc( 1 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by cut;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"B" ) +: ( "" -> hof"A(s)" ) +: Sequent() )
      b ( CutRule( _, Suc( 0 ), _, Ant( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "equality left; upper sequent intro. by left negation inf.; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"A(s)" ) )
      u ( NegLeftRule( _, Suc( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"¬A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[NegLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality left; upper sequent intro. by left negation; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B" ) )
      u ( NegLeftRule( _, Suc( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 2 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[NegLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by right negation inf.;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: ( "" -> hof"B" ) +: Sequent() )
      u ( NegRightRule( _, Ant( 2 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[NegRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by left or inf.; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: Sequent() )
      c OpenAssumption( ( "" -> hof"B(s)" ) +: Sequent() )
      b ( OrLeftRule( _, Ant( 1 ), _, Ant( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y) ∨ B(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by left or inf.; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"B" ) +: Sequent() )
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"C" ) +: Sequent() )
      b ( OrLeftRule( _, Ant( 1 ), _, Ant( 1 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 2 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 1 :: 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by right or inf.;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"B" ) :+ ( "" -> hof"C" ) )
      u ( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[OrRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by left and inf.; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: ( "" -> hof"B(s)" ) +: Sequent() )
      u ( AndLeftRule( _, Ant( 0 ), Ant( 2 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y) & B(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[AndLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by left and inf.; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: ( "" -> hof"s=t" ) +: ( "" -> hof"B" ) +: ( "" -> hof"C" ) +: Sequent() )
      u ( AndLeftRule( _, Ant( 2 ), Ant( 3 ) ) )
      u ( EqualityLeftRule( _, Ant( 2 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[AndLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by right and inf.;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: Sequent() :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"s=t" ) +: Sequent() :+ ( "" -> hof"C" ) )
      b ( AndRightRule( _, Suc( 0 ), _, Suc( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[AndRightRule]
  }

  "equality left; upper sequent intro. by left imp. inf; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( Sequent() :+ ( "" -> hof"A(s)" ) )
      c OpenAssumption( ( "" -> hof"B(s)" ) +: ( "" -> hof"s=t" ) +: Sequent() )
      b ( ImpLeftRule( _, Suc( 0 ), _, Ant( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"A(y) ⊃ B(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: 0 :: Nil ) must beAnInstanceOf[EqualityRightRule]
  }

  "equality left; upper sequent intro. by left imp. inf.; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"A(s)" ) +: Sequent() :+ ( "" -> hof"B" ) )
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"C" ) +: Sequent() )
      b ( ImpLeftRule( _, Suc( 0 ), _, Ant( 1 ) ) )
      u ( EqualityLeftRule( _, Ant( 2 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
    reduction.subProofAt( 0 :: 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by right imp. inf.;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: ( "" -> hof"C" ) +: Sequent() :+ ( "" -> hof"B" ) )
      u ( ImpRightRule( _, Ant( 2 ), Suc( 0 ) ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ImpRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by exists left inf.; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(x, s)" ) +: Sequent() )
      u ( ExistsLeftRule( _, Ant( 1 ), hof"?x A(x, s)", hov"x:i" ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"?x A(x, y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ExistsLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by exists left inf.; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: ( "" -> hof"B(x)" ) +: Sequent() )
      u ( ExistsLeftRule( _, Ant( 2 ), hof"?x B(x)", hov"x:i" ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 2 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ExistsLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by exists right inf.;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: Sequent() :+ ( "" -> hof"B(t)" ) )
      u ( ExistsRightRule( _, Suc( 0 ), hof"?x B(x)", le"t:i" ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ExistsRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by forall left inf.; aux is principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s, s)" ) +: Sequent() )
      u ( ForallLeftRule( _, Ant( 1 ), hof"!x A(x, s)", le"s:i" ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 0 ), Abs( hov"y", le"!x A(x, y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ForallLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by forall left inf.; aux is not principal" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: ( "" -> hof"B(s(x))" ) +: Sequent() )
      u ( ForallLeftRule( _, Ant( 2 ), hof"!x B(x)", le"s(x):i" ) )
      u ( EqualityLeftRule( _, Ant( 1 ), Ant( 2 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ForallLeftRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by forall right inf;" in {
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"s=t" ) +: ( "" -> hof"A(s)" ) +: Sequent() :+ ( "" -> hof"B(x)" ) )
      u ( ForallRightRule( _, Suc( 0 ), hof"!x B(x)", hov"x:i" ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"y", le"A(y):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ForallRightRule]
    reduction.subProofAt( 0 :: Nil ) must beAnInstanceOf[EqualityLeftRule]
  }

  "equality left; upper sequent intro. by induction" in {
    implicit var context = Context()
    context += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    context += hoc"F:nat>o"
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"r=t" ) +: Sequent() :+ ( "" -> hof"F(0)" ) )
      c OpenAssumption( ( "" -> hof"A(r)" ) +: ( "" -> hof"F(x)" ) +: Sequent() :+ ( "" -> hof"F(s(x))" ) )
      b ( ( left, right ) => InductionRule(
        InductionCase( left, hoc"0:nat", Nil, Nil, Suc( 0 ) ) ::
          InductionCase( right, hoc"s:nat>nat", Ant( 1 ) :: Nil, hov"x:nat" :: Nil, Suc( 0 ) ) :: Nil,
        Abs( hov"x:nat", le"F(x)" ), hov"z:nat"
      ) )
      u ( EqualityLeftRule( _, Ant( 0 ), Ant( 1 ), Abs( hov"x:i", le"A(x):o" ) ) ) qed )
    val reduction = equalityLeftReduction( proof.asInstanceOf[EqualityLeftRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "equality right; upper sequent intro. by induction; aux is not principal" in {
    implicit var context = Context()
    context += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    context += hoc"F:nat>o"
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"r=t" ) +: Sequent() :+ ( "" -> hof"F(0)" ) )
      c OpenAssumption( ( "" -> hof"F(x)" ) +: Sequent() :+ ( "" -> hof"F(s(x))" ) :+ ( "" -> hof"A(r)" ) )
      b ( ( left, right ) => InductionRule(
        InductionCase( left, hoc"0:nat", Nil, Nil, Suc( 0 ) ) ::
          InductionCase( right, hoc"s:nat>nat", Ant( 0 ) :: Nil, hov"x:nat" :: Nil, Suc( 0 ) ) :: Nil,
        Abs( hov"x:nat", le"F(x)" ), hov"z:nat"
      ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x:i", le"A(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] ).get
    reduction.conclusion must beMultiSetEqual( proof.conclusion )
    reduction must beAnInstanceOf[ContractionLeftRule]
  }

  "equality right; upper sequent intro. by induction; aux is principal" in {
    implicit var context = Context()
    context += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
    context += hoc"F:nat>o"
    context += hoc"r:nat"
    context += hoc"t:nat"
    val proof = ( ProofBuilder
      c OpenAssumption( ( "" -> hof"r=t" ) +: Sequent() :+ ( "" -> hof"F(0)" ) )
      c OpenAssumption( ( "" -> hof"F(x)" ) +: Sequent() :+ ( "" -> hof"F(s(x))" ) )
      b ( ( left, right ) => InductionRule(
        InductionCase( left, hoc"0:nat", Nil, Nil, Suc( 0 ) ) ::
          InductionCase( right, hoc"s:nat>nat", Ant( 0 ) :: Nil, hov"x:nat" :: Nil, Suc( 0 ) ) :: Nil,
        Abs( hov"x:nat", le"F(x)" ), le"r"
      ) )
      u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), Abs( hov"x:nat", le"F(x):o" ) ) ) qed )
    val reduction = equalityRightReduction( proof.asInstanceOf[EqualityRightRule] )
    reduction must beEmpty
  }
}
