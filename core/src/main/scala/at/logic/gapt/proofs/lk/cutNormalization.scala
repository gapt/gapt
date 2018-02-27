package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.hol.{containsQuantifier, isAtom}
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

  def isRedex(proof: LKProof): Boolean =
    reduce(proof).nonEmpty

  def redexes(proof: LKProof): Seq[LKProof] =
    proof.subProofs.filter { isRedex(_) }.toSeq
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
  def run( proof: LKProof ): LKProof
}

class UppermostRedexReduction( reduction: Reduction ) extends Reduction {
  override def reduce( proof: LKProof ): Option[LKProof] = {
    reduction.reduce( proof ) match {
      case result @ Some( _ ) if !hasUpperRedex( proof ) => result
      case _ => None
    }
  }
  private def hasUpperRedex( proof: LKProof ) = {
    proof.immediateSubProofs.flatMap(_.subProofs).exists( reduction.isRedex( _ ) )
  }
}

class NonPropositionalCutReduction( reduction: CutReduction ) extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    reduction.reduce(cut) match {
      case result @ Some(_) if !containsQuantifier(cut.cutFormula) =>
        result
      case _ => None
    }
  }
}

class UppermostFirstStrategy(reduction: Reduction) extends ReductionStrategy {
  def run( proof: LKProof ): LKProof = {
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

class IterativeParallelStrategy(reduction: Reduction) extends ReductionStrategy {
  override def run( proof: LKProof ): LKProof = {
    var intermediaryProof = proof
    val reducer = (new LowerMostRedexReducer(reduction))
    do {
      reducer.foundRedex = false
      intermediaryProof = reducer.apply( intermediaryProof, () )

    } while ( reducer.foundRedex )
    intermediaryProof
  }
}
trait RedexReducer {
  def foundRedex: Boolean
}

class LowerMostRedexReducer(reduction: Reduction) extends LKVisitor[Unit] with RedexReducer {

  var foundRedex: Boolean = false

  override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
    reduction.reduce( proof ) match {
      case Some( finalProof ) =>
        foundRedex = true
        ( finalProof, SequentConnector.guessInjection(
          fromLower = proof.conclusion, toUpper = finalProof.conclusion ).inv )
      case _ => super.recurse( proof, u )
    }
  }
}

trait Selector {
  def createSelectorReduction(proof: LKProof): Option[Reduction]
}

class IterativeSelectiveStrategy( selector: Selector ) extends ReductionStrategy {
  override def run( proof: LKProof ): LKProof = {
    var intermediaryProof = proof
    var continue = false
    do {
      continue = false
        selector.createSelectorReduction(intermediaryProof) match {
        case Some( selectorReduction ) =>
          continue = true
          intermediaryProof = (new LowerMostRedexReducer(selectorReduction)).apply( intermediaryProof, () )
        case None =>
      }
    } while ( continue )
    intermediaryProof
  }
}

object cutElimination {
  def apply( proof: LKProof ): LKProof =
    (new UppermostFirstStrategy(nonCommutingCutReduction)).run( proof )
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

class MaximumGradeSelector(reduction: CutReduction) extends Selector {
  override def createSelectorReduction(proof: LKProof): Option[Reduction] = {
    maximumGrade(reduction, proof) match {
      case Some(maxGrade) => Some(new MaxGradeReduction(maxGrade, reduction))
      case _ => None
    }
  }

  class MaxGradeReduction(grade: Int, reduction: CutReduction) extends CutReduction {
      override def reduce(cut: CutRule): Option[LKProof] =
        if (logicalComplexity(cut.cutFormula) == grade) {
          reduction.reduce(cut)
        } else {
          None
        }
  }
}

object maximumGrade {
  def apply(reduction: CutReduction, proof: LKProof) : Option[Int] = {
    val cuts: Seq[CutRule] = reduction.redexes(proof) map {
      _ match {
        case cut @ CutRule(_, _, _, _) => cut
      }
    }
    maxGrade(cuts)
  }

  def maxGrade(cuts: Seq[CutRule]): Option[Int] = {
    cuts match {
      case Seq() => None
      case _     => Some(cuts map { cut => logicalComplexity(cut.cutFormula)} max)
    }
  }
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

object ACNFReduction extends CutReduction {
  /**
    * This algorithm implements a generalization of the Gentzen method which
    * reduces all cuts to atomic cuts.
    *
    * @param proof            The proof to subject to cut-elimination.
    * @return The cut-free proof.
    */
  def reduce(proof: CutRule): Option[LKProof] = proof match {
    case cut@CutRule(lsb, l, rsb, _) if !isAtom(lsb.endSequent(l)) && isACNF(lsb) && isACNF(rsb) =>
      if (isAtom(lsb.endSequent(l)))
        (leftRankReduction orElse rightRankReduction).reduce(cut)
      else
        (gradeReduction orElse leftRankReduction orElse rightRankReduction).reduce(cut)
    case _ => None
  }
}

object ACNFTopReduction extends CutReduction {

  import at.logic.gapt.expr.hol.isAtom

  def reduce(proof: CutRule): Option[LKProof] =
    proof match {
      case cut@CutRule(lsb, l, rsb, r) if isAtomicCut(cut) =>
        if (!(introOrCut(lsb, lsb.endSequent(l)) && introOrCut(rsb, rsb.endSequent(r)))) {
          if (introOrCut(lsb, lsb.endSequent(l)))
            rightRankReduction.reduce(cut)
          else
            (leftRankReduction orElse rightRankReduction).reduce(cut)
        } else {
          None
        }
      case cut@CutRule(lsb, _, rsb, _) if isACNFTop(lsb) && isACNFTop(rsb) =>
        (gradeReduction orElse leftRankReduction orElse rightRankReduction).reduce(cut)
      case _ => None
    }

  private def isAtomicCut(cut: CutRule): Boolean = isAtom(cut.cutFormula)
}

object isACNF {
  /**
    * This method checks whether a proof is in ACNF
    *
    * @param proof The proof to check for in ACNF.
    * @return True if proof is in ACNF, False otherwise.
    */
  def apply(proof: LKProof): Boolean = proof match {
    case InitialSequent(_) => true
    case CutRule(lsb, l, rsb, r) =>
      if (isAtom(lsb.endSequent(l))) isACNF(lsb) && isACNF(rsb)
      else false
    case _ => proof.immediateSubProofs.forall(isACNF(_))
  }
}

  object isACNFTop {
    /**
      * This method checks whether a proof is in ACNF top
      *
      * @param proof The proof to check for in ACNF top.
      * @return True if proof is in ACNF,  False otherwise.
      */
    def apply(proof: LKProof): Boolean = proof match {
      case InitialSequent(_) => true
      case CutRule(lsb, l, rsb, r) =>
        if (isAtom(lsb.endSequent(l)))
          if (introOrCut(lsb, lsb.endSequent(l)) && introOrCut(rsb, rsb.endSequent(r)))
            isACNFTop(lsb) && isACNFTop(rsb)
          else false
        else false
      case _ => proof.immediateSubProofs.forall(isACNFTop(_))
    }
  }

  object introOrCut {
    /**
      * Checks if the last rule in proof is a leaf, a cut rule, or a weakening rule on
      * the given formula.
      *
      * @param proof   The proof we are checking.
      * @param formula The formula we are checking.
      * @return True is structure is correct or false if not.
      */
    def apply(proof: LKProof, formula: Formula): Boolean = proof match {
      case LogicalAxiom(_) => true
      case CutRule(lsb, l, rsb, r) => true
      case WeakeningRightRule(_, main) => if (main == formula) true else false
      case WeakeningLeftRule(_, main) => if (main == formula) true else false
      case _ => false
    }
  }