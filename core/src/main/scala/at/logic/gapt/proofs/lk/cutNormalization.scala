package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{All, And, Const, Ex, FOLAtom, Formula, Neg, Or, To}
import at.logic.gapt.proofs.SequentConnector

trait Reduction {
  def reduce( proof: LKProof ): Option[LKProof]
  def orElse( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof ) =
        Reduction.this.reduce( proof ) orElse reduction.reduce( proof )
    }
  def andThen( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof ) =
        Reduction.this.reduce( proof ) flatMap reduction.reduce
    }
}

trait CutReduction extends Reduction {
  def reduce( proof: LKProof ): Option[LKProof] =
    proof match {
      case cut @ CutRule( _, _, _, _ ) => reduce( cut )
      case _                           => None
    }
  def reduce( proof: CutRule ): Option[LKProof]
  def orElse( reduction: CutReduction ): CutReduction =
    new CutReduction {
      def reduce( cut: CutRule ) = CutReduction.this.reduce( cut ) orElse reduction.reduce( cut )
    }
  def andThen( reduction: CutReduction ): CutReduction =
    new CutReduction {
      def reduce( cut: CutRule ) = CutReduction.this.reduce( cut ) flatMap reduction.reduce
    }
}

trait ReductionStrategy {
  def transform( reduction: Reduction, proof: LKProof ): LKProof
}

class UppermostRedexReduction( reduction: Reduction ) extends Reduction {
  override def reduce( proof: LKProof ): Option[LKProof] = {
    reduction.reduce( proof ) match {
      case result @ Some( _ ) if !hasUpperRedex( proof ) => result
      case _ => None
    }
  }
  private def hasUpperRedex( proof: LKProof ) = {
    proof.immediateSubProofs.exists( isRedex( _, reduction ) )
  }

  private def isRedex( proof: LKProof, reduction: Reduction ): Boolean =
    reduction.reduce( proof ).nonEmpty
}

object uppermostFirstStrategy extends ReductionStrategy {
  def transform( reduction: Reduction, proof: LKProof ): LKProof = {
    new LKVisitor[Unit] {
      override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
        val ( intermediaryProof, intermediaryConnector ): ( LKProof, SequentConnector ) = super.recurse( proof, u )
        reduction.reduce( intermediaryProof ) match {
          case Some( intermediaryProof2 ) => {
            val ( finalProof, _ ): ( LKProof, SequentConnector ) = recurse( intermediaryProof2, u )
            ( finalProof, SequentConnector.guessInjection(
              fromLower = proof.conclusion, toUpper = finalProof.conclusion ).inv )
          }
          case None => ( intermediaryProof, intermediaryConnector )
        }
      }
    }.apply( proof, () )
  }
}

object iterativeParallelStrategy extends ReductionStrategy {
  override def transform( reduction: Reduction, proof: LKProof ): LKProof = {
    var intermediaryProof = proof
    var reduced = false
    do {
      reduced = false
      intermediaryProof = new LKVisitor[Unit] {
        override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
          reduction.reduce( proof ) match {
            case Some( finalProof ) =>
              reduced = true
              ( finalProof, SequentConnector.guessInjection(
                fromLower = proof.conclusion, toUpper = finalProof.conclusion ).inv )
            case _ => super.recurse( proof, u )
          }
        }
      }.apply( intermediaryProof, () )
    } while ( reduced )
    intermediaryProof
  }
}

class IterativeSelectiveStrategy( selector: (LKProof, Reduction) => Option[Reduction] ) extends ReductionStrategy {
  override def transform( reduction: Reduction, proof: LKProof ): LKProof = {
    var intermediaryProof = proof
    var continue = false
    do {
      continue = false
        selector(intermediaryProof, reduction) match {
        case Some( selectorReduction ) =>
          continue = true
          intermediaryProof = new LKVisitor[Unit] {
            override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
              selectorReduction.reduce( proof ) match {
                case Some( finalProof ) =>
                  ( finalProof, SequentConnector.guessInjection(
                    fromLower = proof.conclusion, toUpper = finalProof.conclusion ).inv )
                case _ => super.recurse( proof, u )
              }
            }
          }.apply( intermediaryProof, () )
        case None =>
      }
    } while ( continue )
    intermediaryProof
  }

}

object cutElimination {
  def apply( proof: LKProof ): LKProof =
    uppermostFirstStrategy.transform( nonCommutingCutReduction, proof )
}

object logicalComplexity {
  def apply(formula: Formula): Int = {
    formula match {
      case PropAtom(_) => 0
      case FOLAtom(_,_) => 0
      case All(_, subformula) => 1 + logicalComplexity(subformula)
      case Ex(_,subformula) => 1 + logicalComplexity(subformula)
      case And(f1, f2) => 1 + logicalComplexity(f1) + logicalComplexity(f2)
      case Or(f1,f2) => 1 + logicalComplexity(f1) + logicalComplexity(f2)
      case Neg(f1) => 1 + logicalComplexity(f1)
    }
  }
  
  object PropAtom {
    def unapply(arg: Formula): Option[String] = {
      arg match {
        case Const(sym, To, _) => Some(sym)
        case _ => None
      }
    }
  }
}

object maximumGradeSelector {
  def apply(proof: LKProof, reduction: Reduction): Option[Reduction] = {
    maximumGrade(reduction, proof) match {
      case Some(maxGrade) => Some(new CutReduction {
        override def reduce(cut: CutRule): Option[LKProof] =
          if (logicalComplexity(cut.cutFormula) == maxGrade) {
            reduction.reduce(cut)
          } else {
            None
          }
      })
      case _ => None
    }
  }
}

object maximumGrade {
  def apply(reduction: Reduction, proof: LKProof) : Option[Int] = {
    val grades: Set[Int] = proof.subProofs.filter { isRedex(_, reduction) } map { proof =>
      val cut @ CutRule(_,_,_,_) = proof
      logicalComplexity(cut.cutFormula)
    }
    if (grades.isEmpty) {
      None
    } else {
      Some(grades.max)
    }
  }
  private def isRedex( proof: LKProof, reduction: Reduction ): Boolean =
    reduction.reduce( proof ).nonEmpty
}

object nonCommutingCutReduction extends CutReduction {

  override def reduce( cut: CutRule ): Option[LKProof] = reduction.reduce( cut )

  def reduction = gradeReduction orElse
    RightRankWeakeningLeftReduction orElse
    RightRankWeakeningRightReduction orElse
    RightRankContractionLeftReduction orElse
    RightRankContractionRightReduction orElse
    RightRankDefinitionLeftReduction orElse
    RightRankDefinitionRightReduction orElse
    RightRankAndLeftReduction orElse
    RightRankAndRightReduction orElse
    RightRankOrLeftReduction orElse
    RightRankOrRightReduction orElse
    RightRankImpLeftReduction orElse
    RightRankImpRightReduction orElse
    RightRankNegLeftReduction orElse
    RightRankNegRightReduction orElse
    RightRankForallLeftReduction orElse
    RightRankForallRightReduction orElse
    RightRankForallSkRightReduction orElse
    RightRankExistsLeftReduction orElse
    RightRankExistsSkLeftReduction orElse
    RightRankExistsRightReduction orElse
    RightRankEqualityLeftReduction orElse
    RightRankEqualityRightReduction orElse leftRankReduction
}
