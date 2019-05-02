package gapt.proofs.lk.rules

import gapt.expr.Abs
import gapt.expr.BetaReduction
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * An LKProof ending with an induction rule:
 * <pre>
 *   (π,,1,,)   (π,,2,,)           (π,,n,,)
 * case 1      case 2     ...     case n
 * -------------------------------------(ind)
 * Γ :- Δ, F(t: indTy)
 * </pre>
 *
 * This induction rule can handle inductive data types.
 * The cases are proofs that the various type constructors preserve the formula we want to prove.
 * They are provided via the [[InductionCase]] class.
 *
 * @param cases A sequence of proofs showing that each type constructor preserves the validity of the main formula.
 * @param formula The formula we want to prove via induction.
 */
case class InductionRule( cases: Seq[InductionCase], formula: Abs, term: Expr ) extends CommonRule {
  val Abs( quant @ Var( _, indTy ), qfFormula ) = formula
  require( term.ty == indTy )
  cases foreach { c =>
    require( c.indTy == indTy )
    ( c.hypotheses, c.hypVars ).zipped foreach { ( hyp, eigen ) =>
      require( c.proof.endSequent( hyp ) == Substitution( quant -> eigen )( qfFormula ) )
    }
    require( c.proof.endSequent( c.conclusion ) == Substitution( quant -> c.term )( qfFormula ) )
  }
  for ( ( cas, ctx ) <- cases zip contexts )
    require( freeVariables( ctx.elements :+ formula ) intersect cas.eigenVars.toSet isEmpty )

  val mainFormula: Formula = BetaReduction.betaNormalize( formula( term ).asInstanceOf[Formula] )
  override protected def mainFormulaSequent: HOLSequent = Sequent() :+ mainFormula
  override def auxIndices: Seq[Seq[SequentIndex]] = cases map { c => c.hypotheses :+ c.conclusion }
  override def immediateSubProofs: Seq[LKProof] = cases map { _.proof }

  private lazy val product = cases.flatMap { _.productIterator } :+ formula :+ term
  override def productArity: Int = product.size
  override def productElement( n: Int ): Any = product( n )

  override def name: String = "ind"
}
