package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.gaptic._
import gapt.proofs.Context
import gapt.proofs.Sequent
object tautSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += hoc"P: nat>o"
  ctx += PrimRecFun( hoc"PAND:nat>o", "PAND 0 = P 0", "PAND (s i) = (PAND i ∧ P (s i))" )
  ctx += hoc"taut: nat>nat"
  val es = Sequent( Seq( hof"PAND(n)" ), Seq( hof"PAND(n)" ) )
  ctx += Context.ProofNameDeclaration( le"taut n", es )
  val esBc = Sequent( Seq( "Ant_0" -> hof"PAND(0)" ), Seq( "Suc_0" -> hof"PAND(0)" ) )
  val bc = Lemma( esBc ) {
    unfold( "PAND" ) atMost 1 in "Ant_0"
    unfold( "PAND" ) atMost 1 in "Suc_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"taut 0", bc )

  val esSc = Sequent( Seq( "Ant_0" -> hof"PAND(s(n))" ), Seq( "Suc_0" -> hof"PAND(s(n))" ) )
  val sc = Lemma( esSc ) {
    unfold( "PAND" ) atMost 1 in "Ant_0"
    unfold( "PAND" ) atMost 1 in "Suc_0"
    andL
    andR
    ref( "taut" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"taut (s n)", sc )

}

