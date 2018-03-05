package at.logic.gapt.proofs.lk.reductions

import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.{CutRule, LKProof, Selector, logicalComplexity}

class MaximumGradeSelector( reduction: CutReduction, ctx: Context ) extends Selector {
  override def createSelectorReduction( proof: LKProof ): Option[Reduction] = {
    maximumGrade( reduction, proof )(ctx) match {
      case Some( maxGrade ) => Some( new MaxGradeReduction( maxGrade, reduction ) )
      case _                => None
    }
  }

  class MaxGradeReduction( grade: Int, reduction: CutReduction ) extends CutReduction {
    override def reduce( cut: CutRule )( implicit ctx: Context ): Option[LKProof] =
      if ( logicalComplexity( cut.cutFormula ) == grade ) {
        reduction.reduce( cut )
      } else {
        None
      }
  }
}

object maximumGrade {
  def apply( reduction: CutReduction, proof: LKProof )(implicit ctx: Context): Option[Int] = {
    val cuts: Seq[CutRule] = reduction.redexes( proof ) map {
      _ match {
        case cut @ CutRule( _, _, _, _ ) => cut
      }
    }
    maxGrade( cuts )
  }

  def maxGrade( cuts: Seq[CutRule] ): Option[Int] = {
    cuts match {
      case Seq() => None
      case _     => Some( cuts map { cut => logicalComplexity( cut.cutFormula ) } max )
    }
  }
}