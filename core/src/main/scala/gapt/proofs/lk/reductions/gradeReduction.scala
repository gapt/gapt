package gapt.proofs.lk.reductions

import gapt.expr.Bottom
import gapt.expr.Substitution
import gapt.expr.Top
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.DefinitionLeftRule
import gapt.proofs.lk.rules.DefinitionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.SequentConnector
import gapt.proofs.guessPermutation
import gapt.proofs.lk.rules.macros.WeakeningMacroRule

object GradeReductionAxiomLeft extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( LogicalAxiom( _ ), _ ) => Some( cut.rightSubProof )
      case _                        => None
    }
}

object GradeReductionAxiomRight extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( _, LogicalAxiom( _ ) ) => Some( cut.leftSubProof )
      case _                        => None
    }
}

object GradeReductionAxiomTop extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( TopAxiom, WeakeningLeftRule( subProof, Top() ) ) if cut.rightSubProof.mainIndices.head == cut.aux2 =>
        Some( subProof )
      case _ => None
    }
}

object GradeReductionAxiomBottom extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( WeakeningRightRule( subProof, Bottom() ), BottomAxiom ) if cut.leftSubProof.mainIndices.head == cut.aux1 =>
        Some( subProof )
      case _ => None
    }
}

object GradeReductionWeakeningRight extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( l @ WeakeningRightRule( subProof, main ), r ) if l.mainIndices.head == cut.aux1 =>
        // The left cut formula is introduced by weakening
        Some( WeakeningMacroRule( subProof, cut.endSequent ) )
      case _ => None
    }
}

object GradeReductionWeakeningLeft extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( l, r @ WeakeningLeftRule( subProof, main ) ) if cut.aux2 == cut.rightSubProof.mainIndices.head =>
        // The right cut formula is introduced by weakening
        Some( WeakeningMacroRule( subProof, cut.endSequent ) )
      case _ => None
    }
}

object GradeReductionAnd extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( AndRightRule( llSubProof, a1, lrSubProof, a2 ), AndLeftRule( rSubProof, a3, a4 )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        val tmp = CutRule( lrSubProof, a2, rSubProof, a4 )
        val o = tmp.getRightSequentConnector
        Some( CutRule( llSubProof, a1, tmp, o.child( a3 ) ) )

      case _ => None
    }
}

object GradeReductionOr extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( OrRightRule( lSubProof, a1, a2 ), OrLeftRule( rlSubProof, a3, rrSubProof, a4 )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftSequentConnector
        Some( CutRule( tmp, o.child( a2 ), rrSubProof, a4 ) )
      case _ => None
    }
}

object GradeReductionImp extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( ImpRightRule( lSubProof, a1, a2 ), ImpLeftRule( rlSubProof, a3, rrSubProof, a4 )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        val tmp = CutRule( rlSubProof, a3, lSubProof, a1 )
        Some( CutRule( tmp, tmp.getRightSequentConnector.child( a2 ), rrSubProof, a4 ) )
      case _ => None
    }
}

object GradeReductionNeg extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( NegRightRule( lSubProof, a1 ), NegLeftRule( rSubProof, a2 )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        Some( CutRule( rSubProof, a2, lSubProof, a1 ) )

      case _ => None
    }
}

object GradeReductionForall extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( ForallRightRule( lSubProof, a1, eigen, _ ), ForallLeftRule( rSubProof, a2, f, term, _ )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        val lSubProofNew = Substitution( eigen, term )( lSubProof )
        Some( CutRule( lSubProofNew, rSubProof, cut.rightSubProof.auxFormulas.head.head ) )
      case _ => None
    }
}

object GradeReductionExists extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( ExistsRightRule( lSubProof, a2, f, term, _ ), ExistsLeftRule( rSubProof, a1, eigen, _ )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        val rSubProofNew = Substitution( eigen, term )( rSubProof )
        Some( CutRule( lSubProof, rSubProofNew, cut.leftSubProof.auxFormulas.head.head ) )
      case _ => None
    }
}

object GradeReductionDefinition extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( DefinitionRightRule( lSubProof, a1, definition1 ), DefinitionLeftRule( rSubProof, a2, definition2 )
        ) if cut.leftSubProof.mainIndices.head == cut.aux1 && cut.rightSubProof.mainIndices.head == cut.aux2 =>
        Some( CutRule( lSubProof, a1, rSubProof, a2 ) )
      case _ => None
    }
}

object GradeReductionEquality extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    ( cut.leftSubProof, cut.rightSubProof ) match {
      case ( eqL @ EqualityRightRule( _, _, _, _ ), eqR @ EqualityLeftRule( _, _, _, _ )
        ) if eqL.mainIndices.head == cut.aux1 && eqR.mainIndices.head == cut.aux2 && eqL.auxFormula == eqR.auxFormula =>
        Some( CutRule( eqL.subProof, eqL.aux, eqR.subProof, eqR.aux ) )
      case _ => None
    }
}

object gradeReduction extends CutReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the logical complexity of the cut formula or removes the cut.
   *
   * @param cut The proof to which the reduction is applied.
   * @return A reduced proof or None if the reduction could not be applied to the given proof.
   */
  def apply( cut: CutRule ): Option[LKProof] =
    GradeReductionAxiomLeft.reduce( cut ) orElse
      GradeReductionAxiomRight.reduce( cut ) orElse
      GradeReductionAxiomTop.reduce( cut ) orElse
      GradeReductionAxiomBottom.reduce( cut ) orElse
      GradeReductionWeakeningLeft.reduce( cut ) orElse
      GradeReductionWeakeningRight.reduce( cut ) orElse
      GradeReductionAnd.reduce( cut ) orElse
      GradeReductionOr.reduce( cut ) orElse
      GradeReductionImp.reduce( cut ) orElse
      GradeReductionNeg.reduce( cut ) orElse
      GradeReductionForall.reduce( cut ) orElse
      GradeReductionExists.reduce( cut ) orElse
      GradeReductionDefinition.reduce( cut ) orElse
      GradeReductionEquality.reduce( cut )

  override def reduce( proof: CutRule ): Option[LKProof] = apply( proof )
}