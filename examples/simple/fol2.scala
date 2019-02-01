package gapt.examples

import gapt.expr._
import gapt.proofs.ceres.CERES
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.transformations.cutNormal

/**
 * Provides a simple intuitionistic proof of ¬p ∨ p ⊢ ¬¬p → p. Applying the CERES method will create a
 * non-intuitionistic proof but reductive cut-elimination will always create an intuitionistic one. Therefore
 * this is an example that CERES produces cut-free proofs which reductive cut-elimination cannot.
 */
object fol2 {
  val ax = LogicalAxiom( hof"P" )

  val p1 = NegLeftRule( ax, hof"P" )
  val p2 = NegRightRule( p1, hof"P" )
  val p3 = NegLeftRule( p2, hof"-P" )
  val p4 = OrLeftRule( ax, hof"P", p3, hof"-P" )
  val cut_right = ImpRightRule( p4, hof"- -P", hof"P" )

  val p5 = NegLeftRule( ax, hof"P" )
  val p6 = NegRightRule( p5, hof"P" )
  val p7 = OrLeftRule( ax, hof"P", p6, hof"-P" )
  val cut_left = OrRightRule( p7, hof"P", hof"-P" )

  val proof = CutRule( cut_left, cut_right, hof"P | -P" )

  lazy val ceres_cutfree = cutNormal( CERES( proof ) )
  lazy val reductive_cutfree = cutNormal( proof )
}
