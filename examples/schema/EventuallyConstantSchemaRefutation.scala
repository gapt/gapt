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
  val esphi = Sequent( Seq( hof"E(n, f(k)) | LE(f(k), n)", hof"phiSFAT(n)" ), Seq() )
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
    forget( "Ant_0_0_0_0_1" )
    forget( "Ant_0_0_0_0_0" )
    orL( "Ant_0_0_0_0_1_0" )
    orL( "Ant_0_0_0_0_0_0" )
    orL( "Ant_0_0_0_0_1_0" )
    orL( "Ant_0_0_0_0_0_0" )
    allL( "Ant_0_0_1_0", le"z" )
    negL( "Ant_0_0_0_0_0_0" )
    trivial
    allL( "Ant_0_0_1_1_0", le"z" )
    negL( "Ant_0_0_0_0_1_0" )
    trivial
    orL( "Ant_0_0_0_0_0_0" )
    allL( "Ant_0_0_1_0", le"z" )
    negL
    trivial
    allL( "Ant_0_0_1_1_1_0", le"z" )
    orL
    negL
    trivial
    orL
    negL
    trivial
    allL( "Ant_0_0_1_1_1_1", le"z" )
    negL
    trivial
    orL
    allL( "Ant_0_0_1_1_0", le"z" )
    negL
    trivial
    forget( "Ant_0_0_0_0_1_0" )
    forget( "Ant_0_0_1_1_1_0" )
    forget( "Ant_0_0_0_0" )
    allL( "Ant_0_0_0_1", le"(g (g z))" )
    allL( "Ant_0_0_0_1_0", le"(g z)" )
    orL
    negL
    trivial
    orL
    allL( "Ant_0_0_1_0", le"(g z)" )
    negL
    trivial
    ref( "Next" )
    allL( "Ant_0_0_0_1", le"(g z)" )
    allL( "Ant_0_0_0_1_0", le"z" )
    orL( "Ant_0_0_0_1_0_0" )
    negL
    trivial
    orL( "Ant_0_0_0_1_0_0" )
    allL( "Ant_0_0_1_0", le"z" )
    negL( "Ant_0_0_0_1_0_0" )
    trivial
    ref( "Next" )
  }
  val esPR2Sc = Sequent( Seq("Ant_0" -> hof"E(s(n), f(k)) | LE(f(k), s(n))" , "Ant_1" -> hof"phiSFAT(s(n))" ), Seq() )
  val PR2Sc: LKProof = Lemma( esPR2Sc ) {
    unfold( "phiSFAT" ) in "Ant_1"
    andL
    andL
    andL("Ant_1_0_0")
    andL("Ant_1_0_1")
    andL
    andL
  }
}
