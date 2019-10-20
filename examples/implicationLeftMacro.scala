package gapt.examples

import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.proofs.lk._
import gapt.proofs.lk.rules.ImpLeftRule

object implicationLeftMacro {
  /**
   * Iterates the implication left rule.
   *
   * @param left Proofs P₁, ..., Pₙ, where pᵢ has end-sequent Γᵢ ⇒ Δᵢ, Fᵢ for i = 1, ..., n.
   * @param premises Associates Pᵢ with Fᵢ.
   * @param conclusion A formula C.
   * @param right A proof with end-sequent C, Π ⇒ Λ.
   * @return A proof of the end-sequent F₁ → ... → Fₙ → C, Γ₁, ...,Γₙ,Π ⇒ Δ₁,...,Δₙ, Λ.
   */
  def apply(
    left:       Seq[LKProof],
    premises:   Map[LKProof, Formula],
    conclusion: Formula,
    right:      LKProof ): LKProof = {
    left.foldRight( ( conclusion, right ) ) {
      case ( l, ( c, r ) ) =>
        val p = premises( l )
        ( Imp( p, c ), ImpLeftRule( l, p, r, c ) )
    }._2
  }
}

