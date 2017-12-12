package at.logic.gapt.examples

import at.logic.gapt.proofs.{Context, Sequent}
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.ceres.{CLS, CharFormPRN, SchematicStruct, Struct}
import at.logic.gapt.proofs.lk.LKProof

object FunctionInterationRefutation extends TacticsProof( FunctionInterationSchema.ctx ) {
  val SCS: Map[CLS[Nothing], ( Struct[Nothing], Set[Var] )] = SchematicStruct( "phi" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  ctx += hoc"Top:nat>nat"
  ctx += hoc"chi:nat>nat"
  ctx += hoc"rho:nat>nat"
  val esTop = Sequent( Seq( hof"phiSFAFFPR(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val eschi = Sequent( Seq( hof"!A (-P(A) | P(f(A)))", hof"phiSFATFPR(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"chi n", eschi )
  val esrho = Sequent( Seq( hof"!A (-P(A) | P(f(A)))", hof"phiSTATFPR(n)" ), Seq( hof"P(if(n, a))" ) )
  ctx += Context.ProofNameDeclaration( le"rho n", esrho )
  val esPRSc = Sequent( Seq( "Ant_0" -> hof"phiSFAFFPR(s(n))" ), Seq() )
  val PRSc: LKProof = Lemma( esPRSc ) {
    unfold( "phiSFAFFPR" ) in "Ant_0"
    andL
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top (s n)", PRSc )
  val esPRBc = Sequent( Seq( "Ant_0" -> hof"phiSFAFFPR(0)" ), Seq() )
  val PRBc: LKProof = Lemma( esPRBc ) {
    unfold( "phiSFAFFPR" ) in "Ant_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top 0", PRBc )
  val esChiSc = Sequent( Seq(
    "Ant_0" -> hof"!A (-P(A) | P(f(A)))",
    "Ant_1" -> hof"phiSFATFPR(s(n))" ), Seq() )
  val ChiSc: LKProof = Lemma( esChiSc ) {
    unfold( "phiSFATFPR" ) in "Ant_1"
    andL
    allL( "Ant_0", le"(if n a)" )
    orL
    negL( "Ant_0_0" )
    ref( "rho" )
    negL
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n)", ChiSc )
  val esChiBc = Sequent( Seq(
    "Ant_0" -> hof"!A (-P(A) | P(f(A)))",
    "Ant_1" -> hof"phiSFATFPR(0)" ), Seq() )
  val ChiBc: LKProof = Lemma( esChiBc ) {
    unfold( "phiSFATFPR" ) in "Ant_1"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0", ChiBc )
  val esRhoSc = Sequent( Seq(
    "Ant_0" -> hof"!A (-P(A) | P(f(A)))",
    "Ant_1" -> hof"phiSTATFPR(s(n))" ), Seq( "Suc_0" -> hof"P(if(s(n), a))" ) )
  val RhoSc: LKProof = Lemma( esRhoSc ) {
    unfold( "phiSTATFPR" ) in "Ant_1"
    unfold( "if" ) in "Suc_0"
    allL( "Ant_0", le"(if n a)" )
    orL
    negL( "Ant_0_0" )
    ref( "rho" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"rho (s n)", RhoSc )
  val esRhoBc = Sequent( Seq(
    "Ant_0" -> hof"!A (-P(A) | P(f(A)))",
    "Ant_1" -> hof"phiSTATFPR(0)" ), Seq( "Suc_0" -> hof"P(if(0, a))" ) )
  val RhoBc: LKProof = Lemma( esRhoBc ) {
    unfold( "phiSTATFPR" ) in "Ant_1"
    unfold( "if" ) in "Suc_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"rho 0", RhoBc )

}
