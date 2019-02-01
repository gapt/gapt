package gapt.proofs.lk.reductions

import gapt.expr.FOLFormula
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.transformations.Selector
import gapt.proofs.lk.util.logicalComplexity

class MaximumGradeSelector( reduction: CutReduction ) extends Selector {
  override def createSelectorReduction( proof: LKProof ): Option[Reduction] = {
    maximumGrade( reduction, proof ) match {
      case Some( maxGrade ) => Some( new MaxGradeReduction( maxGrade, reduction ) )
      case _                => None
    }
  }

  class MaxGradeReduction( grade: Int, reduction: CutReduction ) extends CutReduction {
    override def reduce( cut: CutRule ): Option[LKProof] =
      if ( logicalComplexity( cut.cutFormula.asInstanceOf[FOLFormula] ) == grade ) {
        reduction.reduce( cut )
      } else {
        None
      }
  }
}

object maximumGrade {
  def apply( reduction: CutReduction, proof: LKProof ): Option[Int] = {
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
      case _     => Some( cuts map { cut => logicalComplexity( cut.cutFormula.asInstanceOf[FOLFormula] ) } max )
    }
  }
}