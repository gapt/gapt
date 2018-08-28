package gapt.examples

import gapt.proofs.{ Sequent }
import gapt.proofs.gaptic._
import gapt.expr._
import gapt.proofs.ceres._
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof

object FunctionIterationRefutation extends TacticsProof( FunctionIterationSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "phi" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  def sequentForm( input: Expr ) = Viperize( le"phiSFAFF $input" )
  ctx += hoc"Top:nat>nat"
  ctx += hoc"chi:nat>nat"
  ctx += hoc"rho:nat>nat"
  val esTop = Sequent( Seq( hof"phiSFAFF(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"Top n", esTop )
  val eschi = Sequent( Seq( hof"!A (-P(A) | P(f(A)))", hof"phiSFATF(n)" ), Seq() )
  ctx += Context.ProofNameDeclaration( le"chi n", eschi )
  val esrho = Sequent( Seq( hof"!A (-P(A) | P(f(A)))", hof"phiSTATF(n)" ), Seq( hof"P(if(n, a))" ) )
  ctx += Context.ProofNameDeclaration( le"rho n", esrho )
  val esPRSc = Sequent( Seq( "Ant_0" -> hof"phiSFAFF(s(n))" ), Seq() )
  val PRSc: LKProof = Lemma( esPRSc ) {
    unfold( "phiSFAFF" ) in "Ant_0"
    andL
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top (s n)", PRSc )
  val esPRBc = Sequent( Seq( "Ant_0" -> hof"phiSFAFF(0)" ), Seq() )
  val PRBc: LKProof = Lemma( esPRBc ) {
    unfold( "phiSFAFF" ) in "Ant_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"Top 0", PRBc )
  val esChiSc = Sequent( Seq(
    "Ant_0" -> hof"!A (-P(A) | P(f(A)))",
    "Ant_1" -> hof"phiSFATF(s(n))" ), Seq() )
  val ChiSc: LKProof = Lemma( esChiSc ) {
    unfold( "phiSFATF" ) in "Ant_1"
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
    "Ant_1" -> hof"phiSFATF(0)" ), Seq() )
  val ChiBc: LKProof = Lemma( esChiBc ) {
    unfold( "phiSFATF" ) in "Ant_1"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0", ChiBc )
  val esRhoSc = Sequent( Seq(
    "Ant_0" -> hof"!A (-P(A) | P(f(A)))",
    "Ant_1" -> hof"phiSTATF(s(n))" ), Seq( "Suc_0" -> hof"P(if(s(n), a))" ) )
  val RhoSc: LKProof = Lemma( esRhoSc ) {
    unfold( "phiSTATF" ) in "Ant_1"
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
    "Ant_1" -> hof"phiSTATF(0)" ), Seq( "Suc_0" -> hof"P(if(0, a))" ) )
  val RhoBc: LKProof = Lemma( esRhoBc ) {
    unfold( "phiSTATF" ) in "Ant_1"
    unfold( "if" ) in "Suc_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"rho 0", RhoBc )

}
