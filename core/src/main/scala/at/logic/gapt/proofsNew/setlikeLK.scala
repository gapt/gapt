package at.logic.gapt.proofsNew

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofsNew.lk.{ Contraction, LKInference, LKProof }
import at.logic.gapt.proofsNew.setlike.{ SetSequent, SetlikeInference }

object setlike {
  case class SetSequent[+A]( sequent: Sequent[A] ) {
    override def equals( that: Any ): Boolean =
      that match {
        case that: SetSequent[b] => this.sequent.setEquals( that.sequent )
        case _                   => false
      }

    override def hashCode: Int =
      ( sequent.antecedent.toSet, sequent.succedent.toSet ).hashCode

    override def toString = sequent.distinct.toString
  }

  case class SetlikeInference[Inf <: SequentInference]( inf: Inf ) extends Inference[SetSequent[HOLFormula]] {
    def premises = inf.premises.map( SetSequent( _ ) )
    def conclusion = SetSequent( inf.conclusion )
  }
}

object setlikeLK {
  type SetlikeLKProof = DagProof[SetSequent[HOLFormula], SetlikeInference[LKInference]]

  def lkToSetlikeLK( lk: LKProof ): SetlikeLKProof =
    lk.flatMap {
      case _: Contraction => Seq()
      case inf            => Seq( SetlikeInference( inf ) )
    }
}