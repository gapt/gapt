package gapt.proofs.lk.reductions

import gapt.expr.{ Substitution, freeVariables, rename }
import gapt.proofs.context.Context
import gapt.proofs.lk.{ AndLeftRule, AndRightRule, ContractionLeftRule, ContractionMacroRule, ContractionRightRule, CutRule, DefinitionLeftRule, DefinitionRightRule, EqualityLeftRule, EqualityRightRule, ExistsLeftRule, ExistsRightRule, ExistsSkLeftRule, ForallLeftRule, ForallRightRule, ForallSkRightRule, ImpLeftRule, ImpRightRule, InductionCase, InductionRule, LKProof, NegLeftRule, NegRightRule, OrLeftRule, OrRightRule, WeakeningLeftRule, WeakeningMacroRule, WeakeningRightRule, inductionEigenvariables }
import gapt.proofs.{ SequentConnector, guessPermutation }

object LeftRankWeakeningLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ WeakeningLeftRule( subProof, main ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        Some( WeakeningLeftRule( cutSub, main ) )
      case _ => None
    }
}

object LeftRankWeakeningRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ WeakeningRightRule( subProof, main ) =>
        Some(
          WeakeningRightRule(
            CutRule(
              subProof, l.getSequentConnector.parent( cut.aux1 ),
              cut.rightSubProof, cut.aux2 ),
            main ) )
      case _ => None
    }
}

object LeftRankContractionLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ContractionLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val ( a1New, a2New ) = (
          cutSub.getLeftSequentConnector.child( a1 ),
          cutSub.getLeftSequentConnector.child( a2 ) )
        Some( ContractionLeftRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object LeftRankContractionRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ContractionRightRule( subProof, a1, a2 ) =>
        if ( l.mainIndices.head == cut.aux1 ) {
          // The left cut formula is the main formula of the contraction: Duplicate right proof
          val tmp = CutRule( subProof, a1, cut.rightSubProof, cut.aux2 )
          val tmp2 = CutRule( tmp, tmp.getLeftSequentConnector.child( a2 ), cut.rightSubProof, cut.aux2 )
          Some(
            ContractionMacroRule(
              tmp2,
              cut.leftSubProof.endSequent.delete( cut.aux1 ) ++ cut.rightSubProof.endSequent.delete( cut.aux2 ) ) )
        } else { // The contraction operates on the context: Swap the inferences
          val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
          val cutSub = CutRule( subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
          val a1New = cutSub.getLeftSequentConnector.child( a1 )
          val a2New = cutSub.getLeftSequentConnector.child( a2 )
          Some( ContractionRightRule( cutSub, a1New, a2New ) )
        }

      case _ => None
    }
}

object LeftRankCutReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( CutRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( CutRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankDefinitionLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ DefinitionLeftRule( subProof, a, m ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )

      case _ => None
    }
}

object LeftRankDefinitionRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ DefinitionRightRule( subProof, a, m ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( DefinitionRightRule( cutSub, aNew, m ) )

      case _ => None
    }
}

object LeftRankAndLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ AndLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val a1New = cutSub.getLeftSequentConnector.child( a1 )
        val a2New = cutSub.getLeftSequentConnector.child( a2 )
        Some( AndLeftRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}
object LeftRankAndRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( AndRightRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( AndRightRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankOrLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( OrLeftRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( OrLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankOrRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ OrRightRule( subProof, a1, a2 ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val a1New = cutSub.getLeftSequentConnector.child( a1 )
        val a2New = cutSub.getLeftSequentConnector.child( a2 )
        Some( OrRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object LeftRankImpLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( ImpLeftRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankImpRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ImpRightRule( subProof, a1, a2 ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val a1New = cutSub.getLeftSequentConnector.child( a1 )
        val a2New = cutSub.getLeftSequentConnector.child( a2 )
        Some( ImpRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object LeftRankNegLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ NegLeftRule( subProof, a ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( NegLeftRule( cutSub, aNew ) )

      case _ => None
    }
}

object LeftRankNegRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ NegRightRule( subProof, a ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( NegRightRule( cutSub, aNew ) )

      case _ => None
    }
}

object LeftRankForallLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ForallLeftRule( subProof, a, f, term, quant ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallLeftRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object LeftRankForallRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ForallRightRule( _, _, _, _
        ) if cut.leftSubProof.mainIndices.head != cut.aux1 && freeVariables( cut.endSequent ).contains( l.eigenVariable ) =>
        val newEigenvariable = rename( l.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( l.eigenVariable -> newEigenvariable )
        val newLeftSubProof = l.copy( subProof = renaming( l.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( leftSubProof = newLeftSubProof ) )

      case left @ ForallRightRule( _, _, _, _ ) if left.mainIndices.head != cut.aux1 =>
        val newSubProof = CutRule(
          left.subProof,
          left.getSequentConnector.parent( cut.aux1 ),
          cut.rightSubProof,
          cut.aux2 )
        Some( left.copy(
          subProof = newSubProof,
          aux = newSubProof.getLeftSequentConnector.child( left.aux ) ) )

      case _ => None
    }
}

object LeftRankForallSkRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ForallSkRightRule( subProof, a, main, skTerm ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallSkRightRule( cutSub, aNew, main, skTerm ) )

      case _ => None
    }
}

object LeftRankExistsLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case left @ ExistsLeftRule( _, _, _, _ ) if freeVariables( cut.endSequent ).contains( left.eigenVariable ) =>
        val newEigenvariable = rename( left.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( left.eigenVariable -> newEigenvariable )
        val newLeftSubProof = left.copy( subProof = renaming( left.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( leftSubProof = newLeftSubProof ) )

      case left @ ExistsLeftRule( _, _, _, _ ) =>
        val newSubProof = CutRule(
          left.subProof,
          left.getSequentConnector.parent( cut.aux1 ),
          cut.rightSubProof,
          cut.aux2 )
        Some( left.copy(
          subProof = newSubProof,
          aux = newSubProof.getLeftSequentConnector.child( left.aux ) ) )
      case _ => None
    }
}

object LeftRankExistsSkLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ExistsSkLeftRule( subProof, a, main, skTerm ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsSkLeftRule( cutSub, aNew, main, skTerm ) )

      case _ => None
    }
}

object LeftRankExistsRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ExistsRightRule( subProof, a, f, term, quant ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsRightRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object LeftRankEqualityLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ EqualityLeftRule( subProof, eq, aux, indicator ) =>
        val conn1 = l.getSequentConnector
        val cutSub = CutRule( subProof, conn1.parent( cut.aux1 ), cut.rightSubProof, cut.aux2 )
        val conn2 = cutSub.getLeftSequentConnector
        Some( EqualityLeftRule( cutSub, conn2.child( eq ), conn2.child( aux ), indicator ) )

      case _ => None
    }
}

object LeftRankEqualityRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ EqualityRightRule( subProof, eq, eaux, indicator ) if l.mainIndices.head != cut.aux1 =>
        val conn1 = l.getSequentConnector
        val cutSub = CutRule( subProof, conn1.parent( cut.aux1 ), cut.rightSubProof, cut.aux2 )
        val conn2 = cutSub.getLeftSequentConnector
        Some( EqualityRightRule( cutSub, conn2.child( eq ), conn2.child( eaux ), indicator ) )
      case _ => None
    }
}

object LeftRankInductionReduction extends CutReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces a cut by moving the cut towards the proof's leaves.
   * @param cut The cut to be reduced.
   * @param ctx The proof's context.
   * @return A reduced proof if the given cut is reducible w.r.t to some induction inference,
   *         otherwise None.
   */
  def apply( cut: CutRule ): Option[LKProof] = {

    cut.leftSubProof match {
      case ind @ InductionRule( _, _, _ ) if ind.mainIndices.head != cut.aux1 &&
        ( contextVariables( cut ) intersect inductionEigenvariables( ind ) nonEmpty ) =>
        val newEigenvariables = rename( inductionEigenvariables( ind ), contextVariables( cut ) )
        val newInductionCases = ind.cases map { inductionCase =>
          val newCaseEigenvariables = inductionCase.eigenVars.map( newEigenvariables )
          val renaming = Substitution( inductionCase.eigenVars.map { ev => ( ev, newEigenvariables( ev ) ) } )
          inductionCase.copy( proof = renaming( inductionCase.proof ), eigenVars = newCaseEigenvariables )
        }
        val newLeftSubProof = ind.copy( cases = newInductionCases )
        apply( cut.copy( leftSubProof = newLeftSubProof ) )

      case ind @ InductionRule( inductionCases, inductionFormula, inductionTerm
        ) if ind.mainIndices.head != cut.aux1 =>
        val newInductionCases = inductionCases zip ind.occConnectors map {
          case ( inductionCase, connector ) =>
            if ( connector.parentOption( cut.aux1 ).nonEmpty ) {
              val subProof = CutRule(
                inductionCase.proof, connector.parent( cut.aux1 ), cut.rightSubProof, cut.aux2 )
              val hypotheses = inductionCase.hypotheses map { subProof.getLeftSequentConnector.child( _ ) }
              val conclusion = subProof.getLeftSequentConnector.child( inductionCase.conclusion )
              inductionCase.copy( proof = subProof, hypotheses = hypotheses, conclusion = conclusion )
            } else {
              inductionCase
            }
        }
        Some( InductionRule( newInductionCases, inductionFormula, inductionTerm ) )
      case _ => None
    }
  }

  private def contextVariables( cut: CutRule ) =
    freeVariables( cut.rightSubProof.endSequent ) ++ freeVariables( cut.leftSubProof.endSequent )

  override def reduce( proof: CutRule ): Option[LKProof] = apply( proof )
}

object leftRankReduction extends CutReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the rank of the cut by permuting it upwards on the left-hand side.
   *
   * @param cut The proof to which the left rank reduction is applied
   * @return A reduced proof or None if the left rank reduction could not be applied.
   */
  def apply( cut: CutRule ): Option[LKProof] =
    LeftRankWeakeningLeftReduction.reduce( cut ) orElse
      LeftRankWeakeningRightReduction.reduce( cut ) orElse
      LeftRankContractionLeftReduction.reduce( cut ) orElse
      LeftRankContractionRightReduction.reduce( cut ) orElse
      LeftRankCutReduction.reduce( cut ) orElse
      LeftRankDefinitionLeftReduction.reduce( cut ) orElse
      LeftRankDefinitionRightReduction.reduce( cut ) orElse
      LeftRankAndLeftReduction.reduce( cut ) orElse
      LeftRankAndRightReduction.reduce( cut ) orElse
      LeftRankOrLeftReduction.reduce( cut ) orElse
      LeftRankOrRightReduction.reduce( cut ) orElse
      LeftRankImpLeftReduction.reduce( cut ) orElse
      LeftRankImpRightReduction.reduce( cut ) orElse
      LeftRankNegLeftReduction.reduce( cut ) orElse
      LeftRankNegRightReduction.reduce( cut ) orElse
      LeftRankForallLeftReduction.reduce( cut ) orElse
      LeftRankForallRightReduction.reduce( cut ) orElse
      LeftRankForallSkRightReduction.reduce( cut ) orElse
      LeftRankExistsLeftReduction.reduce( cut ) orElse
      LeftRankExistsSkLeftReduction.reduce( cut ) orElse
      LeftRankExistsRightReduction.reduce( cut ) orElse
      LeftRankEqualityLeftReduction.reduce( cut ) orElse
      LeftRankEqualityRightReduction.reduce( cut )

  override def reduce( proof: CutRule ): Option[LKProof] = apply( proof )
}

object RightRankWeakeningRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case weakening @ WeakeningRightRule( _, _ ) =>
        val aux2Sub = weakening.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, weakening.subProof, aux2Sub )
        Some( WeakeningRightRule( cutSub, weakening.mainFormula ) )
      case _ => None
    }
}

object RightRankWeakeningLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case weakening @ WeakeningLeftRule( _, _ ) =>
        if ( cut.aux2 == cut.rightSubProof.mainIndices.head ) {
          Some( WeakeningMacroRule( weakening.subProof, cut.endSequent ) )
        } else {
          Some(
            WeakeningLeftRule(
              CutRule(
                cut.leftSubProof,
                cut.aux1,
                weakening.subProof,
                weakening.getSequentConnector.parent( cut.aux2 ) ),
              weakening.mainFormula ) )
        }
      case _ => None
    }
}

object RightRankContractionLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ContractionLeftRule( subProof, a1, a2 ) =>
        if ( r.mainIndices.head == cut.aux2 ) {
          // The right cut formula is the main formula of the contraction: Duplicate left proof
          val tmp = CutRule( cut.leftSubProof, cut.aux1, subProof, a1 )
          val tmp2 = CutRule( cut.leftSubProof, cut.aux1, tmp, tmp.getRightSequentConnector.child( a2 ) )
          Some(
            ContractionMacroRule(
              tmp2,
              cut.leftSubProof.endSequent.delete( cut.aux1 ) ++ cut.rightSubProof.endSequent.delete( cut.aux2 ) ) )
        } else {
          // The contraction operates on the context: Swap the inferences
          val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
          val cutSub = CutRule( cut.leftSubProof, cut.aux1, subProof, aux2Sub )
          val a1New = cutSub.getRightSequentConnector.child( a1 )
          val a2New = cutSub.getRightSequentConnector.child( a2 )
          Some( ContractionLeftRule( cutSub, a1New, a2New ) )
        }
      case _ => None
    }
}

object RightRankContractionRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ContractionRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( ContractionRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object RightRankCutReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case upperCut @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = upperCut.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = upperCut.getRightSequentConnector.parents( cut.aux2 )
        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( CutRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )
          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( CutRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }
      case _ => None
    }
}

object RightRankDefinitionLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case definition @ DefinitionLeftRule( subProof, a, m ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = definition.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, definition.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )
      case _ => None
    }
}

object RightRankDefinitionRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case definition @ DefinitionRightRule( subProof, a, m ) =>
        val aux2Sub = definition.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, definition.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )
      case _ => None
    }
}

object RightRankAndLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case and @ AndLeftRule( subProof, a1, a2 ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = and.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, and.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( AndLeftRule( cutSub, a1New, a2New ) )
      case _ => None
    }
}

object RightRankAndRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = r.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = r.getRightSequentConnector.parents( cut.aux2 )

        ( aux2Left, aux2Right ) match {
          // The right cut formula is in the left subproof of the binary inference
          case ( Seq( aux2Sub ), Seq() ) =>
            val cutSub = CutRule(
              cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( AndRightRule(
              cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          // The right cut formula is in the right subproof of the binary inference
          case ( Seq(), Seq( aux2Sub ) ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( AndRightRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }
      case _ => None
    }
}

object RightRankOrLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Left = r.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = r.getRightSequentConnector.parents( cut.aux2 )

        ( aux2Left, aux2Right ) match {
          // The right cut formula is in the left subproof of the binary inference
          case ( Seq( aux2Sub ), Seq() ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( OrLeftRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          // The right cut formula is in the right subproof of the binary inference
          case ( Seq(), Seq( aux2Sub ) ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( OrLeftRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object RightRankOrRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ OrRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( OrRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object RightRankImpLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Left = r.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = r.getRightSequentConnector.parents( cut.aux2 )

        ( aux2Left, aux2Right ) match {
          // The right cut formula is in the left subproof of the binary inference
          case ( Seq( aux2Sub ), Seq() ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( ImpLeftRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          // The right cut formula is in the right subproof of the binary inference
          case ( Seq(), Seq( aux2Sub ) ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object RightRankImpRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ImpRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( ImpRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object RightRankNegLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ NegLeftRule( subProof, a ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( NegLeftRule( cutSub, aNew ) )

      case _ => None
    }
}

object RightRankNegRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ NegRightRule( subProof, a ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( NegRightRule( cutSub, aNew ) )

      case _ => None
    }
}

object RightRankForallLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ForallLeftRule( subProof, a, f, term, quant ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallLeftRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object RightRankForallRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case right @ ForallRightRule( _, _, _, _ ) if freeVariables( cut.endSequent ).contains( right.eigenVariable ) =>
        val newEigenvariable = rename( right.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( right.eigenVariable -> newEigenvariable )
        val newRightSubProof = right.copy(
          subProof = renaming( right.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( rightSubProof = newRightSubProof ) )

      case right @ ForallRightRule( _, _, _, _ ) =>
        val newSubProof = CutRule(
          cut.leftSubProof,
          cut.aux1,
          right.subProof,
          right.getSequentConnector.parent( cut.aux2 ) )
        Some( right.copy(
          subProof = newSubProof,
          aux = newSubProof.getRightSequentConnector.child( right.aux ) ) )

      case _ => None
    }
}

object RightRankForallSkRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ForallSkRightRule( subProof, a, main, skTerm ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallSkRightRule( cutSub, aNew, main, skTerm ) )

      case _ => None
    }
}

object RightRankExistsLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case right @ ExistsLeftRule( _, _, _, _
        ) if right.mainIndices.head != cut.aux2 && freeVariables( cut.endSequent ).contains( right.eigenVariable ) =>
        val newEigenvariable = rename( right.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( right.eigenVariable -> newEigenvariable )
        val newRightSubProof = right.copy( subProof = renaming( right.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( rightSubProof = newRightSubProof ) )

      case right @ ExistsLeftRule( _, _, _, _ ) if right.mainIndices.head != cut.aux2 =>
        val newSubProof = CutRule(
          cut.leftSubProof,
          cut.aux1,
          right.subProof,
          right.getSequentConnector.parent( cut.aux2 ) )
        Some( right.copy(
          subProof = newSubProof,
          aux = newSubProof.getRightSequentConnector.child( right.aux ) ) )

      case _ => None
    }
}

object RightRankExistsSkLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ExistsSkLeftRule( subProof, a, main, skTerm ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsSkLeftRule( cutSub, aNew, main, skTerm ) )

      case _ => None
    }
}

object RightRankExistsRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ExistsRightRule( subProof, a, f, term, quant ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsRightRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object RightRankEqualityLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ EqualityLeftRule( subProof, eq, eaux, indicator
        ) if r.mainIndices.head != cut.aux2 && r.eqInConclusion != cut.aux2 =>
        val conn1 = r.getSequentConnector
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, subProof, conn1.parent( cut.aux2 ) )
        val conn2 = cutSub.getRightSequentConnector
        Some( EqualityLeftRule( cutSub, conn2.child( eq ), conn2.child( eaux ), indicator ) )

      case _ => None
    }
}

object RightRankEqualityRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ EqualityRightRule( subProof, eq, eaux, indicator ) if r.eqInConclusion != cut.aux2 =>
        val conn1 = r.getSequentConnector
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, subProof, conn1.parent( cut.aux2 ) )
        val conn2 = cutSub.getRightSequentConnector
        Some( EqualityRightRule( cutSub, conn2 child eq, conn2 child eaux, indicator ) )

      case _ => None
    }
}

object RightRankInductionReduction extends CutReduction {

  override def reduce( cut: CutRule ): Option[LKProof] = apply( cut )

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the complexity of a cut w.r.t. to an induction inference by
   * moving the cut over the induction inference.
   * @param cut The cut that is to be reduced.
   * @return A reduced proof if the cut is reducible, otherwise None.
   */
  def apply( cut: CutRule ): Option[LKProof] = {

    cut.rightSubProof match {

      case ind @ InductionRule( _, _, _
        ) if contextVariables( cut ) intersect inductionEigenvariables( ind ) nonEmpty =>
        val newEigenvariables = rename( inductionEigenvariables( ind ), contextVariables( cut ) )
        val newInductionCases = ind.cases map { inductionCase =>
          val newCaseEigenvariables = inductionCase.eigenVars.map( newEigenvariables )
          val renaming = Substitution( inductionCase.eigenVars.map { ev => ( ev, newEigenvariables( ev ) ) } )
          inductionCase.copy( proof = renaming( inductionCase.proof ), eigenVars = newCaseEigenvariables )
        }
        val newRightSubProof = ind.copy( cases = newInductionCases )
        apply( cut.copy( rightSubProof = newRightSubProof ) )

      case ind @ InductionRule( _, indFormula, indTerm ) =>
        val targetCase = ind.cases.filter( _.proof.endSequent.antecedent.contains( cut.cutFormula ) ).head
        val newIndCases = ind.cases map {
          indCase =>
            if ( indCase == targetCase ) {
              val subProof = CutRule( cut.leftSubProof, indCase.proof, cut.cutFormula )
              val hypIndices = indCase.hypotheses.map( subProof.getRightSequentConnector.child( _ ) )
              val conclIndex = subProof.getRightSequentConnector.child( indCase.conclusion )
              InductionCase( subProof, indCase.constructor, hypIndices, indCase.eigenVars, conclIndex )
            } else {
              indCase
            }
        }
        Some( InductionRule( newIndCases, indFormula, indTerm ) )
      case _ => None
    }
  }

  private def contextVariables( cut: CutRule ) =
    freeVariables( cut.rightSubProof.endSequent ) ++ freeVariables( cut.leftSubProof.endSequent )
}

object rightRankReduction extends CutReduction {

  def reduce( cut: CutRule ): Option[LKProof] = apply( cut )

  def applyWithSequentConnector( cut: CutRule )( implicit ctx: Context ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the rank of the cut by permuting it upwards on the right-hand side.
   *
   * @param cut The proof to which the right rank reduction is applied
   * @return A reduced proof or None if no right reduction could be applied to the proof.
   */
  def apply( cut: CutRule ): Option[LKProof] =
    RightRankWeakeningLeftReduction.reduce( cut ) orElse
      RightRankWeakeningRightReduction.reduce( cut ) orElse
      RightRankContractionLeftReduction.reduce( cut ) orElse
      RightRankContractionRightReduction.reduce( cut ) orElse
      RightRankCutReduction.reduce( cut ) orElse
      RightRankDefinitionLeftReduction.reduce( cut ) orElse
      RightRankDefinitionRightReduction.reduce( cut ) orElse
      RightRankAndLeftReduction.reduce( cut ) orElse
      RightRankAndRightReduction.reduce( cut ) orElse
      RightRankOrLeftReduction.reduce( cut ) orElse
      RightRankOrRightReduction.reduce( cut ) orElse
      RightRankImpLeftReduction.reduce( cut ) orElse
      RightRankImpRightReduction.reduce( cut ) orElse
      RightRankNegLeftReduction.reduce( cut ) orElse
      RightRankNegRightReduction.reduce( cut ) orElse
      RightRankForallLeftReduction.reduce( cut ) orElse
      RightRankForallRightReduction.reduce( cut ) orElse
      RightRankForallSkRightReduction.reduce( cut ) orElse
      RightRankExistsLeftReduction.reduce( cut ) orElse
      RightRankExistsSkLeftReduction.reduce( cut ) orElse
      RightRankExistsRightReduction.reduce( cut ) orElse
      RightRankEqualityLeftReduction.reduce( cut ) orElse
      RightRankEqualityRightReduction.reduce( cut )
}