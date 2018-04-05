package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof

object VeryWeakPHPRefutation extends TacticsProof( VeryWeakPHPSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "omega" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  ctx += hoc"Top:nat>nat"
  ctx += hoc"Seq1Make:nat>nat>nat"
  ctx += hoc"Seq2Make:nat>nat>nat"
  ctx += hoc"Seq1Make2:nat>nat>nat"
  ctx += hoc"Seq2Make2:nat>nat>nat"
  ctx += hoc"Next:nat>nat"

  ctx += PrimRecFun( hoc"SW:nat>i", "SW 0  = z ", "SW (s y) = (suc (SW y))" )
  ctx += PrimRecFun(
    hoc"SEQ1:nat>nat>o",
    "SEQ1 0 y = ((E y (f (suc (SW 0)))) | (LE (f (SW 0)) y))",
    "SEQ1 (s x) y = (( (E y (f (suc (SW (s x))))) | (LE (f (SW (s x))) y) )  & (SEQ1 x y))" )
  ctx += PrimRecFun(
    hoc"SEQ2:nat>nat>o",
    "SEQ2 0 y = ((E y (f (SW 0))) | (LE (f (SW 0)) y))",
    "SEQ2 (s x) y = (( (E y (f (SW (s x)))) | (LE (f (SW (s x))) y) ) & (SEQ2 x y))" )

  val esTop = Sequent( Seq( hof"omegaSFAF(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val esSeq1Make = Sequent(
    Seq( hof" !a ((E(n, f(suc(a))) | LE(f(a), n)))" ),
    Seq( hof"SEQ1(k, n)" ) )
  ctx += Context.ProofNameDeclaration( le"Seq1Make k n", esSeq1Make )
  val esSeq2Make = Sequent(
    Seq( hof" !a ((E(n, f(a)) | LE(f(a), n)))" ),
    Seq( hof"SEQ2(k, n)" ) )
  ctx += Context.ProofNameDeclaration( le"Seq2Make k n", esSeq2Make )
  val esSeq1Make2 = Sequent(
    Seq(
      hof"SEQ1(k, s(n))",
      hof"SEQ2(k, s(n))",
      hof"E(n, f(suc(SW(k)))) | LE(f(SW(k)), n)",
      hof"!b (¬LE(f(suc(b)), s(n)) ∨ (E(n, f(suc(b))) ∨ LE(f(b), n)))",
      hof"!a (¬E(s(n), f(a)) ∨ ¬E(s(n), f(suc(a))))" ),
    Seq( hof"SEQ1(k, n)" ) )
  ctx += Context.ProofNameDeclaration( le"Seq1Make2 k n", esSeq1Make2 )
  val esSeq2Make2 = Sequent(
    Seq(
      hof"SEQ1(k, s(n))",
      hof"SEQ2(k, s(n))",
      hof"!b (¬LE(f(b), s(n)) ∨ (E(n, f(b)) ∨ LE(f(b), n)))",
      hof"!a (¬E(s(n), f(a)) ∨ ¬E(s(n), f(suc(a))))" ),
    Seq( hof"SEQ2(k, n)" ) )
  ctx += Context.ProofNameDeclaration( le"Seq2Make2 k n", esSeq2Make2 )
  val esNext = Sequent(
    Seq( hof"SEQ1(n, n)", hof"SEQ2(n, n)", hof"phiSFAT(n)" ),
    Seq() )
  ctx += Context.ProofNameDeclaration( le"Next n", esNext )
  val esPRBc = Sequent( Seq( "Ant_0" -> hof"omegaSFAF(0)" ), Seq() )
  val PRBc: LKProof = Lemma( esPRBc ) {
    unfold( "omegaSFAF" ) in "Ant_0"
    unfold( "phiSFAT" ) in "Ant_0"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top 0", PRBc )

  val esPRSc = Sequent( Seq( "Ant_0" -> hof"omegaSFAF(s(n))" ), Seq() )
  val PRSc: LKProof = Lemma( esPRSc ) {
    unfold( "omegaSFAF" ) in "Ant_0"
    andL
    andL
    cut( "cut", hof"SEQ1(s(n),s(n)) & SEQ2(s(n),s(n))" )
    andR
    ref( "Seq1Make" )
    ref( "Seq2Make" )
    andL
    ref( "Next" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top (s n)", PRSc )

  val esNextBc = Sequent( Seq(
    "Ant_0" -> hof"phiSFAT(0)",
    "Ant_1" -> hof"SEQ1(0, 0)",
    "Ant_2" -> hof"SEQ2(0,0)" ), Seq() )
  val NextBc: LKProof = Lemma( esNextBc ) {
    unfold( "phiSFAT" ) in "Ant_0"
    unfold( "SEQ1" ) in "Ant_1"
    unfold( "SEQ2" ) in "Ant_2"
    unfold( "SW" ) in "Ant_1"
    unfold( "SW" ) in "Ant_2"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Next 0", NextBc )
  val esNextSc = Sequent( Seq(
    "Ant_0" -> hof"phiSFAT(s(n))",
    "Ant_1" -> hof"SEQ1(s(n),s(n))",
    "Ant_2" -> hof"SEQ2(s(n),s(n))" ), Seq() )
  val NextSc: LKProof = Lemma( esNextSc ) {
    unfold( "phiSFAT" ) in "Ant_0"
    andL
    andL
    andL
    cut( "cut", hof"SEQ1(n,n) & SEQ2(n,n)" )
    andR
    unfold( "SEQ1" ) in "Ant_1"
    andL
    unfold( "SEQ2" ) in "Ant_2"
    andL
    allL( "Ant_0_0_0", le"(SW (s n))" )
    orL( "Ant_2_0" )
    orL( "Ant_1_0" )
    orL( "Ant_0_0_0_0" )
    negL
    trivial
    negL
    trivial
    unfold( "SW" ) in "Ant_1_0"
    allL( "Ant_0_0_1_1", le"(SW n)" )
    orL( "Ant_0_0_1_1_0" )
    negL
    trivial
    ref( "Seq1Make2" )
    unfold( "SW" ) in "Ant_2_0"
    allL( "Ant_0_0_1_1", le"(SW n)" )
    orL( "Ant_0_0_1_1_0" )
    negL
    trivial
    ref( "Seq1Make2" )
    unfold( "SEQ1" ) in "Ant_1"
    andL
    unfold( "SEQ2" ) in "Ant_2"
    andL
    allL( "Ant_0_0_0", le"(SW (s n))" )
    orL( "Ant_2_0" )
    orL( "Ant_1_0" )
    orL( "Ant_0_0_0_0" )
    negL
    trivial
    negL
    trivial
    ref( "Seq2Make2" )
    ref( "Seq2Make2" )
    andL
    ref( "Next" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Next (s n)", NextSc )

  val esSeq2Make2Bc = Sequent( Seq(
    "Ant_0" -> hof"SEQ1(0, s(n))",
    "Ant_1" -> hof"SEQ2(0, s(n))",
    "Ant_2" -> hof"!b (¬LE(f(b), s(n)) ∨ (E(n, f(b)) ∨ LE(f(b), n)))",
    "Ant_3" -> hof"!a (¬E(s(n), f(a)) ∨ ¬E(s(n), f(suc(a))))" ), Seq(
    "Suc_0" -> hof"SEQ2(0, n)" ) )
  val Seq2Make2Bc: LKProof = Lemma( esSeq2Make2Bc ) {
    unfold( "SEQ1" ) in "Ant_0"
    unfold( "SEQ2" ) in "Ant_1"
    unfold( "SEQ2" ) in "Suc_0"
    unfold( "SW" ) in "Ant_0"
    unfold( "SW" ) in "Ant_1"
    unfold( "SW" ) in "Suc_0"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq2Make2 0 n", Seq2Make2Bc )

  val esSeq2Make2Sc = Sequent( Seq(
    "Ant_0" -> hof"SEQ1(s(k), s(n))",
    "Ant_1" -> hof"SEQ2(s(k), s(n))",
    "Ant_2" -> hof"!b (¬LE(f(b), s(n)) ∨ (E(n, f(b)) ∨ LE(f(b), n)))",
    "Ant_3" -> hof"!a (¬E(s(n), f(a)) ∨ ¬E(s(n), f(suc(a))))" ), Seq(
    "Suc_0" -> hof"SEQ2(s(k), n)" ) )
  val Seq2Make2Sc: LKProof = Lemma( esSeq2Make2Sc ) {
    unfold( "SEQ1" ) in "Ant_0"
    unfold( "SW" ) in "Ant_0"
    andL
    unfold( "SEQ2" ) in "Ant_1"
    unfold( "SW" ) in "Ant_1"
    andL
    unfold( "SEQ2" ) in "Suc_0"
    unfold( "SW" ) in "Suc_0"
    andR
    orL( "Ant_1_0" )
    orL( "Ant_0_0" )
    allL( "Ant_3", le"(suc (SW k))" )
    orL
    negL
    trivial
    negL
    trivial
    allL( "Ant_2", le"(suc (SW k))" )
    orL
    negL
    trivial
    orR
    orL
    trivial
    trivial
    allL( "Ant_2", le"(suc (SW k))" )
    orL( "Ant_2_0" )
    negL
    trivial
    orR
    orL( "Ant_2_0" )
    trivial
    trivial
    ref( "Seq2Make2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq2Make2 (s k) n", Seq2Make2Sc )

  val esSeq1Make2Bc = Sequent( Seq(
    "Ant_0" -> hof"SEQ1(0, s(n))",
    "Ant_1" -> hof"SEQ2(0, s(n))",
    "Ant_2" -> hof"!b (¬LE(f(suc(b)), s(n)) ∨ (E(n, f(suc(b))) ∨ LE(f(b), n)))",
    "Ant_3" -> hof"!a (¬E(s(n), f(a)) ∨ ¬E(s(n), f(suc(a))))",
    "Ant_4" -> hof"E(n, f(suc(SW(0)))) | LE(f(SW(0)), n)" ), Seq(
    "Suc_0" -> hof"SEQ1(0, n)" ) )
  val Seq1Make2Bc: LKProof = Lemma( esSeq1Make2Bc ) {
    unfold( "SEQ1" ) in "Ant_0"
    unfold( "SEQ2" ) in "Ant_1"
    unfold( "SEQ1" ) in "Suc_0"
    unfold( "SW" ) in "Ant_0"
    unfold( "SW" ) in "Ant_1"
    unfold( "SW" ) in "Suc_0"
    unfold( "SW" ) in "Ant_4"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq1Make2 0 n", Seq1Make2Bc )

  val esSeq1Make2Sc = Sequent( Seq(
    "Ant_0" -> hof"SEQ1(s(k), s(n))",
    "Ant_1" -> hof"SEQ2(s(k), s(n))",
    "Ant_2" -> hof"!b (¬LE(f(suc(b)), s(n)) ∨ (E(n, f(suc(b))) ∨ LE(f(b), n)))",
    "Ant_3" -> hof"!a (¬E(s(n), f(a)) ∨ ¬E(s(n), f(suc(a))))",
    "Ant_4" -> hof"E(n, f(suc(SW(s(k))))) | LE(f(SW(s(k))), n)" ), Seq(
    "Suc_0" -> hof"SEQ1(s(k), n)" ) )
  val Seq1Make2Sc: LKProof = Lemma( esSeq1Make2Sc ) {
    unfold( "SW" ) in "Ant_4"
    unfold( "SEQ1" ) in "Ant_0"
    unfold( "SW" ) in "Ant_0"
    andL
    unfold( "SEQ2" ) in "Ant_1"
    unfold( "SW" ) in "Ant_1"
    andL
    unfold( "SEQ1" ) in "Suc_0"
    unfold( "SW" ) in "Suc_0"
    andR
    orR
    orL( "Ant_4" )
    trivial
    trivial
    orL( "Ant_1_0" )
    orL( "Ant_0_0" )
    allL( "Ant_3", le"(suc(SW k))" )
    orL( "Ant_3_0" )
    negL
    trivial
    negL
    trivial
    allL( "Ant_2", le"(SW k)" )
    orL( "Ant_2_0" )
    negL
    trivial
    allL( "Ant_2", le"(SW k)" )
    orL( "Ant_2_1" )
    negL
    trivial
    ref( "Seq1Make2" )
    allL( "Ant_2", le"(SW k)" )
    orL( "Ant_2_0" )
    negL
    trivial
    ref( "Seq1Make2" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq1Make2 (s k) n", Seq1Make2Sc )

  val esSeq1MakeBc = Sequent(
    Seq( "Ant_0" -> hof" !a ((E(n, f(suc(a))) | LE(f(a), n)))" ), Seq(
      "Suc_0" -> hof"SEQ1(0, n)" ) )
  val Seq1MakeBc: LKProof = Lemma( esSeq1MakeBc ) {
    unfold( "SEQ1" ) in "Suc_0"
    unfold( "SW" ) in "Suc_0"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq1Make 0 n ", Seq1MakeBc )
  val esSeq1MakeSc = Sequent(
    Seq( "Ant_0" -> hof" !a ((E(n, f(suc(a))) | LE(f(a), n)))" ), Seq(
      "Suc_0" -> hof"SEQ1(s(k), n)" ) )
  val Seq1MakeSc: LKProof = Lemma( esSeq1MakeSc ) {
    unfold( "SEQ1" ) in "Suc_0"
    unfold( "SW" ) in "Suc_0"
    andR
    allL( le"(suc (SW k))" )
    orR
    orL
    trivial
    trivial
    ref( "Seq1Make" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq1Make (s k) n", Seq1MakeSc )

  val esSeq2MakeBc = Sequent(
    Seq( "Ant_0" -> hof" !a ((E(n, f(a)) | LE(f(a), n)))" ), Seq(
      "Suc_0" -> hof"SEQ2(0, n)" ) )
  val Seq2MakeBc: LKProof = Lemma( esSeq2MakeBc ) {
    unfold( "SEQ2" ) in "Suc_0"
    unfold( "SW" ) in "Suc_0"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq2Make 0 n ", Seq2MakeBc )
  val esSeq2MakeSc = Sequent(
    Seq( "Ant_0" -> hof" !a ((E(n, f(a)) | LE(f(a), n)))" ), Seq(
      "Suc_0" -> hof"SEQ2(s(k), n)" ) )
  val Seq2MakeSc: LKProof = Lemma( esSeq2MakeSc ) {
    unfold( "SEQ2" ) in "Suc_0"
    unfold( "SW" ) in "Suc_0"
    andR
    allL( le"(suc (SW k))" )
    orR
    orL
    trivial
    trivial
    ref( "Seq2Make" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Seq2Make (s k) n", Seq2MakeSc )
}
