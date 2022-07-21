package gapt.examples.sequence

import gapt.expr._
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.proofs.Ant
import gapt.proofs.Suc
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.allR
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.impR
import gapt.proofs.gaptic.include
import gapt.proofs.gaptic.prop
import gapt.proofs.gaptic.repeat
import gapt.proofs.gaptic.trivial
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.macros.WeakeningMacroRule

/**
 * Constructs short FOL LK proofs of the sequents
 *
 * P(0), ∀x. P(x) → P(s(x)) :- P(s^2 ^n^ ^(0))
 *
 * where n is an Integer parameter >= 0.
 */
object LinearCutExampleProof extends ProofSequence {
  private val ax = fof"!x (P x -> P (s x))"
  private def s( n: Int )( x: FOLTerm ): FOLTerm =
    if ( n == 0 ) x else s( n - 1 )( FOLFunction( "s", x ) )
  private def lemma( n: Int ): LKProof =
    Proof( hols"h: !x (P(x) -> P(${s( 1 << ( n - 1 ) )( fov"x" )})) :- !x (P(x) -> P(${s( 1 << n )( fov"x" )}))" ) {
      allR; impR; repeat( chain( "h" ) ); trivial
    }

  /**
   * @param n An integer >= 0.
   * @param left Which way to associate the cuts.
   * @return A proof of P(0), ∀x. P(x) → P(s(x)) :- P(s^2 ^m^ ^(0))
   */
  def apply( n: Int, left: Boolean ): LKProof = {
    require( n >= 0, "n must be nonnegative" )
    val ls = ( 1 until n ).map( lemma ) :+
      Proof( hols"p0: P(0), lem: !x (P(x) -> P(${s( 1 << math.max( 0, n - 1 ) )( fov"x" )})) :- g: P(${s( 1 << n )( foc"0" )})" ) {
        repeat( chain( "lem" ) )
        trivial
      }
    val cut = CutRule( _: LKProof, Suc( 0 ), _: LKProof, Ant( 0 ) )
    WeakeningMacroRule(
      if ( left ) ls.reduceLeft( cut ) else ls.reduceRight( cut ),
      hos"P(0), $ax :- P(${s( 1 << n )( foc"0" )})" )
  }

  def apply( n: Int ): LKProof = apply( n, left = true )
}

object LinearRightCutExampleProof extends ProofSequence {
  def apply( n: Int ): LKProof = LinearCutExampleProof( n, left = false )
}
