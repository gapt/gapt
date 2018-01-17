package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof

object EventuallyConstantSchemaRefutation extends TacticsProof( EventuallyConstantSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "phi" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  ctx += hoc"Top:nat>nat"
  ctx += hoc"Next:nat>i>nat"
  val esTop = Sequent( Seq( hof"phiSFAF(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val esphi = Sequent( Seq( hof"E(n, f(g(k))) | LE(f(g(k)), n)", hof"E(n, f(k)) | LE(f(k), n)", hof"phiSFAT(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"Next n k", esphi )

  val esPRSc = Sequent( Seq( "Ant_0" -> hof"phiSFAF(s(n))" ), Seq() )
  val PRSc: LKProof = Lemma( esPRSc ) {
    unfold( "phiSFAF" ) in "Ant_0"
    andL
    andL
    andL( "Ant_0_0_0" )
    andL( "Ant_0_0_1" )
    andL
    andL
    allL( "Ant_0_0_0_0", le"(g z)" )
    allL( "Ant_0_0_0_0_0", le"z" )
    allL( "Ant_0_0_0_0", le"z" )
    allL( "Ant_0_0_0_0_1", le"z" )
    orL( "Ant_0_0_0_0_1_0" )
    orL( "Ant_0_0_0_0_0_0" )
    escargot
    orL( "Ant_0_0_0_0_1_0" )
    escargot
    allL( "Ant_0_0_1_1_1_0", le"z" )
    orL
    escargot
    allL( "Ant_0_0_0_1", le"(g (g z))" )
    allL( "Ant_0_0_0_1", le"(g z)" )
    allL( "Ant_0_0_0_1_0", le"(g z)" )
    allL( "Ant_0_0_0_1_1", le"(g z)" )
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    ref( "Next" )
    allL( "Ant_0_0_0_1", le"(g z)" )
    allL( "Ant_0_0_0_1", le"z" )
    allL( "Ant_0_0_0_1_0", le"z" )
    allL( "Ant_0_0_0_1_1", le"z" )
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    ref( "Next" )
  }
  val esPRBc = Sequent( Seq( "Ant_0" -> hof"phiSFAF(0)" ), Seq() )
  val PRBc: LKProof = Lemma( esPRBc ) {
    unfold( "phiSFAF" ) in "Ant_0"
    escargot
  }
  val esPR2Sc = Sequent( Seq(
    "Ant_2" -> hof"E(s(n), f(g(k))) | LE(f(g(k)), s(n))",
    "Ant_1" -> hof"E(s(n), f(k)) | LE(f(k), s(n))",
    "Ant_0" -> hof"phiSFAT(s(n))" ), Seq() )
  val PR2Sc: LKProof = Lemma( esPR2Sc ) {
    unfold( "phiSFAT" ) in "Ant_0"
    andL
    andL
    andL( "Ant_0_0_0" )
    andL( "Ant_0_0_1" )
    andL
    andL
    allL( "Ant_0_0_1_1_1_0", le"k" )
    orL( "Ant_0_0_1_1_1_0_0" )
    orL( "Ant_1" )
    escargot
    allL( "Ant_0_0_1_1_1_0", le"(g k)" )
    orL( "Ant_0_0_1_1_1_0_1" )
    orL( "Ant_2" )
    escargot
    allL( "Ant_0_0_0_1", le"(g (g k))" )
    allL( "Ant_0_0_0_1", le"(g k)" )
    allL( "Ant_0_0_0_1_0", le"(g k)" )
    allL( "Ant_0_0_0_1_1", le"k" )
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    ref( "Next" )
    allL( "Ant_0_0_0_1", le"(g k)" )
    allL( "Ant_0_0_0_1", le"k" )
    allL( "Ant_0_0_0_1_0", le"k" )
    allL( "Ant_0_0_0_1_1", le"k" )
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    ref( "Next" )
    orL( "Ant_0_0_1_1_1_0_0" )
    orL( "Ant_2" )
    escargot
    allL( "Ant_0_0_0_1", le"(g (g k))" )
    allL( "Ant_0_0_0_1", le"(g k)" )
    allL( "Ant_0_0_0_1_0", le"(g k)" )
    allL( "Ant_0_0_0_1_1", le"(g k)" )
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    orL( "Ant_0_0_0_1_1_0" )
    escargot
    orL( "Ant_0_0_0_1_0_0" )
    escargot
    ref( "Next" )
    escargot
  }
  val esPR2Bc = Sequent( Seq(
    "Ant_2" -> hof"E(0, f(g(k))) | LE(f(g(k)), 0)",
    "Ant_1" -> hof"E(0, f(k)) | LE(f(k), 0)",
    "Ant_0" -> hof"phiSFAT(0)" ), Seq() )
  val PR2Bc: LKProof = Lemma( esPR2Bc ) {
    unfold( "phiSFAT" ) in "Ant_0"
    escargot
  }
}
