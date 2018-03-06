package at.logic.gapt.proofs.lk.reductions

import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.{CutRule, LKProof}

trait RedexFilter {
  def filter(reduction: Reduction): Reduction
}

class UppermostRedexFilter extends RedexFilter {

  override def filter(reduction: Reduction): Reduction =
    new Reduction {
      override def reduce(proof: LKProof): Option[LKProof] =
        reduction.reduce(proof) match {
          case result@Some(_) if !hasUpperRedex(proof) => result
          case _ => None
        }
      private def hasUpperRedex(proof: LKProof) = {
        proof.immediateSubProofs.flatMap(_.subProofs).exists(reduction.isRedex(_))
      }
    }
}

class NonPropositionalCutFilter extends RedexFilter {
  override def filter(reduction: Reduction): Reduction =
    new Reduction {
      override def reduce(proof: LKProof): Option[LKProof] = {
        proof match {
          case cut@CutRule(_, _, _, _) => reduction.reduce(cut) match {
            case result@Some(_) if !containsQuantifier(cut.cutFormula) =>
              result
            case _ => None
          }
          case _ => reduction.reduce(proof)
        }
      }
    }
}

