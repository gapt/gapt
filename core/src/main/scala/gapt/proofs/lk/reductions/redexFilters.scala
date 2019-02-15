package gapt.proofs.lk.reductions

import gapt.expr.formula.hol.containsQuantifier
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule

trait RedexFilter {
  def filter( reduction: Reduction ): Reduction
}

class UppermostRedexFilter extends RedexFilter {

  override def filter( reduction: Reduction ): Reduction =
    new Reduction {
      override def reduce( proof: LKProof ): Option[LKProof] =
        reduction.reduce( proof ) match {
          case result @ Some( _ ) if !hasUpperRedex( proof ) => result
          case _ => None
        }
      private def hasUpperRedex( proof: LKProof ) = {
        proof.immediateSubProofs.flatMap( _.subProofs ).exists( reduction.isRedex( _ ) )
      }
    }
}

class NonPropositionalCutFilter extends RedexFilter {
  override def filter( reduction: Reduction ): Reduction =
    new Reduction {
      override def reduce( proof: LKProof ): Option[LKProof] = {
        proof match {
          case cut @ CutRule( _, _, _, _ ) => reduction.reduce( cut ) match {
            case result @ Some( _ ) if !containsQuantifier( cut.cutFormula ) =>
              result
            case _ => None
          }
          case _ => reduction.reduce( proof )
        }
      }
    }
}

