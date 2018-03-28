package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{Context, Sequent}
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof


object VeryWeakPHPRefutation extends TacticsProof( VeryWeakPHPSchema.ctx ){
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "omega" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  ctx += hoc"Top:nat>nat"
  ctx += hoc"Next:nat>nat"
  ctx += PrimRecFun( hoc"ss:nat>i", "ss 0 = z ", "ss (s y) = (suc (ss y))" )

  // print(ctx.normalizer.rules.toString())
  val esTop = Sequent( Seq( hof"omegaSFAF(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val esphi = Sequent( Seq(
    hof"E(n, f(ss(n))) | LE(f(ss(n)), n)",
    hof"E(n, f(suc(ss(n)))) | LE(f(ss(n)), n)",
    hof"phiSFAT(n)"), Seq() )
  ctx += Context.ProofNameDeclaration( le"Next n", esphi )
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
    unfold( "phiSFAT" ) in "Ant_0_1"
    andL
    andL
    andL
    allL("Ant_0_0_0", le"(ss (s n))")
    allL("Ant_0_1_0_0",le"(ss (s n))")
    allL("Ant_0_0_0", le"(ss n)")
    allL("Ant_0_1_0_0",le"(ss n)")
    orL("Ant_0_1_0_0_0")
    orL("Ant_0_1_0_0_1")
    orL("Ant_0_0_0_1")
    negL("Ant_0_1_0_0_1")
    trivial
    orL("Ant_0_0_0_0")
    negL("Ant_0_1_0_0_0")
    trivial
    allL("Ant_0_1_0_1_0",le"(ss n)")
    allL("Ant_0_1_0_1_1",le"(ss n)")
    orL("Ant_0_1_0_1_0_0")
    negL("Ant_0_1_0_1_0_0")
    trivial
    unfold("ss") in "Ant_0_0_0_0"
    orL("Ant_0_1_0_1_1_0")
    negL("Ant_0_1_0_1_1_0")
    trivial
    ref("Next")
    orL("Ant_0_0_0_0")
    negL("Ant_0_1_0_0_0")
    trivial
    unfold("ss") in "Ant_0_0_0_0"
    allL("Ant_0_1_0_1_1",le"(ss n)")
    orL("Ant_0_1_0_1_1_0")
    negL("Ant_0_1_0_1_1_0")
    trivial
    allL("Ant_0_0_1",le"(ss n)")
    orL("Ant_0_0_1_0")
    negL("Ant_0_1_0_0_1")
    trivial
    allL("Ant_0_1_0_1_0",le"(ss n)")
    orL("Ant_0_1_0_1_0_0")
    negL("Ant_0_1_0_1_0_0")
    trivial
    ref("Next")
    orL("Ant_0_1_0_0_1")
    orL("Ant_0_0_0_1")
    negL("Ant_0_1_0_0_1")
    trivial
    allL("Ant_0_0_1",le"(ss (s n))")
    unfold("ss") in "Ant_0_0_1_0"
    unfold("ss") in "Ant_0_1_0_0_0"
    orL("Ant_0_0_1_0")
    negL("Ant_0_1_0_0_0")
    trivial
    allL("Ant_0_1_0_1_1",le"(ss n)")
    orL("Ant_0_1_0_1_1_0")
    negL("Ant_0_1_0_1_1_0")
    trivial
    allL("Ant_0_1_0_1_0",le"(ss n)")
    orL("Ant_0_1_0_1_0_0")
    negL("Ant_0_1_0_1_0_0")
    trivial
    ref("Next")
    allL("Ant_0_0_0",le"(ss (s n))")
    unfold("ss") in "Ant_0_0_0_2"
    orL("Ant_0_0_0_2")
    negL("Ant_0_1_0_0_1")
    trivial
    allL("Ant_0_1_0_1_1",le"(ss n)")
    orL("Ant_0_1_0_1_1_0")
    negL("Ant_0_1_0_1_1_0")
    trivial
    allL("Ant_0_0_1",le"(ss n)")
    orL("Ant_0_0_1_0")
    negL("Ant_0_1_0_0_1")
    trivial
    allL("Ant_0_1_0_1_0",le"(ss n)")
    orL("Ant_0_1_0_1_0_0")
    negL("Ant_0_1_0_1_0_0")
    trivial
    ref("Next")
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top (s n)", PRSc )

  val esPR2Bc = Sequent( Seq(
   "Ant_0"-> hof"E(0, f(suc(ss(0)))) | LE(f(ss(0)), 0)",
    "Ant_1"-> hof"E(0, f(ss(0))) | LE(f(ss(0)), 0)",
    "Ant_3"-> hof"phiSFAT(0)"), Seq() )
  val PR2Bc: LKProof = Lemma( esPR2Bc ) {
    unfold( "ss" ) in "Ant_0"
    unfold( "ss" ) in "Ant_1"
    unfold( "phiSFAT" ) in "Ant_3"
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"Next 0", PR2Bc )

  val esPR2Sc = Sequent( Seq(
    "Ant_0"-> hof"E(s(n), f(suc(ss(s(n))))) | LE(f(ss(s(n))), s(n))",
    "Ant_1"-> hof"E(s(n), f(ss(s(n)))) | LE(f(ss(s(n))), s(n))",
    "Ant_3"-> hof"phiSFAT(s(n))"), Seq() )
  val PR2Sc: LKProof = Lemma( esPR2Sc ) {

    unfold( "phiSFAT" ) in "Ant_3"
    andL
    andL
    andL
  }
  ctx += Context.ProofDefinitionDeclaration( le"Next (s n)", PR2Sc )
}
