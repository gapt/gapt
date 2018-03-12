package gapt.examples

import gapt.proofs.gaptic._
import gapt.expr._
import gapt.proofs.{ Context, Sequent }
import gapt.proofs.ceres.{ CLS, CharFormPRP, SchematicStruct, Struct }
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.lk.LKProof

object FunctionIterationRefutationPos extends TacticsProof( FunctionIterationSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "phi" ).getOrElse( Map() )
  val CFPRP = CharFormPRP( SCS )
  CharFormPRP.PR( CFPRP )
  ctx += hoc"Top:nat>nat"
  ctx += hoc"chi:nat>nat"
  ctx += hoc"rho:nat>nat"
  val esTop = Sequent( Seq(), Seq( hof"phiSFAFF(n)" ) )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val eschi = Sequent( Seq(), Seq( hof"?A (P(A) & -P(f(A)))", hof"phiSFATF(n)" ) )
  ctx += Context.ProofNameDeclaration( le"chi n", eschi )
  val esrho = Sequent( Seq(), Seq( hof"?A (P(A) & -P(f(A)))", hof"P(if(n, a))", hof"phiSTATF(n)" ) )
  ctx += Context.ProofNameDeclaration( le"rho n", esrho )

  val esPRSc = Sequent( Seq(), Seq( "Suc_0" -> hof"phiSFAFF(s(n))" ) )
  val PRSc: LKProof = Lemma( esPRSc ) {
    unfold( "phiSFAFF" ) in "Suc_0"
    orR
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top (s n)", PRSc )
  val esPRBc = Sequent( Seq(), Seq( "Suc_0" -> hof"phiSFAFF(0)" ) )
  val PRBc: LKProof = Lemma( esPRBc ) {
    unfold( "phiSFAFF" ) in "Suc_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top 0", PRBc )
  val esChiSc = Sequent( Seq(), Seq(
    "Suc_0" -> hof"?A (P(A) & -P(f(A)))",
    "Suc_1" -> hof"phiSFATF(s(n))" ) )
  val ChiSc: LKProof = Lemma( esChiSc ) {
    unfold( "phiSFATF" ) in "Suc_1"
    orR
    exR( "Suc_0", le"(if n a)" )
    andR
    ref( "rho" )
    negR( "Suc_0_0" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n)", ChiSc )
  val esChiBc = Sequent( Seq(), Seq(
    "Suc_0" -> hof"?A (P(A) & -P(f(A)))",
    "Suc_1" -> hof"phiSFATF(0)" ) )
  val ChiBc: LKProof = Lemma( esChiBc ) {
    unfold( "phiSFATF" ) in "Suc_1"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0", ChiBc )

  val esRhoSc = Sequent( Seq(), Seq( "Suc_0" -> hof"?A (P(A) & -P(f(A)))", "Suc_1" -> hof"P(if(s(n), a))", "Suc_2" -> hof"phiSTATF(s(n))" ) )
  val RhoSc: LKProof = Lemma( esRhoSc ) {
    unfold( "phiSTATF" ) in "Suc_2"
    unfold( "if" ) in "Suc_1"
    exR( "Suc_0", le"(if n a)" )
    andR
    ref( "rho" )
    negR
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"rho (s n)", RhoSc )
  val esRhoBc = Sequent( Seq(), Seq( "Suc_0" -> hof"?A (P(A) & -P(f(A)))", "Suc_1" -> hof"P(if(0, a))", "Suc_2" -> hof"phiSTATF(0)" ) )
  val RhoBc: LKProof = Lemma( esRhoBc ) {
    unfold( "phiSTATF" ) in "Suc_2"
    unfold( "if" ) in "Suc_1"
    negR
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"rho 0", RhoBc )
}
