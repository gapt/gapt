package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr.{ Abs, All, And, Ex, Expr, Formula, Imp, Neg, Or, Substitution, Var, freeVariables, rename }
import at.logic.gapt.proofs.{ Ant, Context, SequentConnector, SequentIndex, Suc }

class pushEqualityInferencesToLeaves {

  /**
   * Moves equality inferences to the leaves.
   *
   * @param proof The proof to which the transformation is to be applied.
   * @param ctx Defines constants, types, etc.
   * @return A proof with equality inferences moved towards the leaves as far as possible.
   */
  def pushEqualitiesToLeaves( proof: LKProof )( implicit ctx: Context ): LKProof = {
    var newProof = PushWeakeningToLeaves( proof )
    var previousNewProof = proof
    do {
      previousNewProof = newProof
      newProof = moveEqualitiesToLeaves( newProof, false )
      newProof = PushWeakeningToLeaves( newProof )
    } while ( previousNewProof != newProof && newProof.subProofs.exists( equalityReduction( _ ).isDefined ) )
    newProof
  }

  /**
   * Applies an equality reduction to the last inference rule of the given proof.
   * @param proof The proof to which this reduction is applied.
   * @return A reduced proof and a sequent connector if last inference of the given proof
   *         is a topmost reducible equality inference. Otherwise, None is returned.
   */
  def equalityReduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = proof match {
    case eq @ EqualityLeftRule( _, _, _, _ ) if isUpperMostRedex( eq ) =>
      equalityLeftReduction( eq ).map { guessPermutation( proof, _ ) }
    case eq @ EqualityRightRule( _, _, _, _ ) if isUpperMostRedex( eq ) =>
      equalityRightReduction( eq ).map { guessPermutation( proof, _ ) }
    case _ => None
  }

  /**
   * Returns the proper subproofs of the given proof.
   * @param proof The proof whose subproofs are to be computed.
   * @return The proof's proper subproofs.
   */
  private def properSubProofs( proof: LKProof ) = proof.immediateSubProofs.flatMap( _.subProofs )

  /**
   * Checks whether the given proof's last inference is an uppermost redex for the equality reduction.
   * @param proof The proof that is to be checked.
   * @return true if the last inference is an uppermost redex for the equality reduction, false otherwise.
   */
  private def isUpperMostRedex( proof: LKProof ): Boolean = !properSubProofs( proof ).exists( equalityReduction( _ ).isDefined )

  /**
   * Exhaustively applies the equality reduction.
   * @param proof The proof to which the reduction is applied.
   * @param cleanStructRules If true the structural rules are cleaned after each step.
   * @param ctx Defines constants, types, etc.
   * @return A proof which does not contain any redex for the equality reduction. The reduction may have
   *         introduced new weakening inferences.
   */
  def moveEqualitiesToLeaves( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ): LKProof = {
    def terminateReduction( proof: LKProof ) = proof.subProofs.forall( equalityReduction( _ ).isEmpty )
    ( new ReductiveCutElimination() )( proof, terminateReduction, equalityReduction, cleanStructRules )
  }

}

object equalityRightReduction {

  /**
   * Tries to move the given equality inference upwards.
   * @param equality The equality inference to which the reduction is applied.
   * @return Either a reduced proof if the reduction could be applied, or None.
   */
  def apply( equality: EqualityRightRule ): Option[LKProof] = {
    equality.subProof match {

      case weakening @ WeakeningLeftRule( subProof, _ ) if weakening.mainIndices.head != equality.eq =>
        val connector = weakening.getSequentConnector
        val newEquality = new EqualityRightRule(
          subProof,
          connector.parent( equality.eq ),
          connector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( WeakeningLeftRule( newEquality, weakening.formula ) )

      case weakening @ WeakeningRightRule( subProof, _ ) =>
        if ( weakening.mainIndices.head == equality.aux ) {
          Some( WeakeningRightRule( subProof, equality.mainFormula ) )
        } else {
          val connector = weakening.getSequentConnector
          val newEquality = new EqualityRightRule(
            subProof,
            connector.parent( equality.eq ),
            connector.parent( equality.aux ),
            equality.replacementContext
          )
          Some( WeakeningRightRule( newEquality, weakening.formula ) )
        }

      case contraction @ ContractionLeftRule( subProof, _, _ ) =>
        val connector = contraction.getSequentConnector
        val newEquality = EqualityRightRule(
          subProof,
          connector.parents( equality.eq ).head,
          connector.parent( equality.aux ),
          equality.replacementContext
        )
        val connector2 = newEquality.getSequentConnector
        Some( ContractionLeftRule( newEquality, connector2.child( contraction.aux1 ), connector2.child( contraction.aux2 ) ) )

      case contraction @ ContractionRightRule( _, _, _ ) =>
        val contractionConnector = contraction.getSequentConnector
        if ( contraction.mainIndices.head != equality.aux ) {
          val newEquality = EqualityRightRule(
            contraction.subProof,
            contractionConnector.parent( equality.eq ),
            contractionConnector.parent( equality.aux ),
            equality.replacementContext
          )
          Some( ContractionRightRule(
            newEquality,
            newEquality.getSequentConnector.child( contraction.aux1 ),
            newEquality.getSequentConnector.child( contraction.aux2 )
          ) )
        } else {
          val newEquality1 = EqualityRightRule(
            contraction.subProof,
            contractionConnector.parent( equality.eq ),
            contractionConnector.parents( equality.aux )( 0 ),
            equality.replacementContext
          )
          val equalityConnector = newEquality1.getSequentConnector
          val newEquality2 = EqualityRightRule(
            newEquality1,
            equalityConnector.child( contractionConnector.parent( equality.eq ) ),
            equalityConnector.child( contractionConnector.parents( equality.aux )( 1 ) ),
            equality.replacementContext
          )
          val endConnector = newEquality2.getSequentConnector * equalityConnector
          Some( ContractionRightRule(
            newEquality2,
            endConnector.child( contraction.aux1 ),
            endConnector.child( contraction.aux2 )
          ) )
        }

      case cut @ CutRule( _, _, _, _ ) =>
        val Seq( ( newLeftSubProof, leftConnector ), ( newRightSubProof, rightConnector ) ) = splitEquality(
          equality,
          ( cut.leftSubProof, cut.getLeftSequentConnector, equality.replacementContext ) ::
            ( cut.rightSubProof, cut.getRightSequentConnector, equality.replacementContext ) :: Nil
        )
        val newSubProof = CutRule(
          newLeftSubProof, leftConnector.child( cut.aux1 ), newRightSubProof, rightConnector.child( cut.aux2 )
        )
        Some( ContractionMacroRule( newSubProof, equality.conclusion, false ) )

      case neg @ NegLeftRule( _, _ ) =>
        val negConnector = neg.getSequentConnector
        val newEquality = EqualityRightRule(
          neg.subProof,
          negConnector.parent( equality.eq ),
          negConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( NegLeftRule( newEquality, newEquality.getSequentConnector.child( neg.aux ) ) )

      case neg @ NegRightRule( _, _ ) =>
        val context =
          if ( neg.mainIndices.head != equality.aux ) {
            equality.replacementContext
          } else {
            val Abs( variable, Neg( formula ) ) = equality.replacementContext
            Abs( variable, formula )
          }
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality, ( neg.subProof, neg.getSequentConnector, context ) :: Nil
        )
        Some( NegRightRule( newSubProof, subConnector.child( neg.aux ) ) )

      case and @ AndLeftRule( _, _, _ ) =>
        val andConnector = and.getSequentConnector
        val newEquality = EqualityRightRule(
          and.subProof,
          andConnector.parent( equality.eq ),
          andConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( AndLeftRule(
          newEquality,
          newEquality.getSequentConnector.child( and.aux1 ),
          newEquality.getSequentConnector.child( and.aux2 )
        ) )

      case and @ AndRightRule( left, aux1, right, aux2 ) =>
        val ( leftContext, rightContext ) =
          if ( and.mainIndices.head != equality.aux ) {
            ( equality.replacementContext, equality.replacementContext )
          } else {
            val Abs( variable, And( leftFormula, rightFormula ) ) = equality.replacementContext
            ( Abs( variable, leftFormula ), Abs( variable, rightFormula ) )
          }
        val Seq( ( newLeftSubProof, leftConnector ), ( newRightSubProof, rightConnector ) ) = splitEquality(
          equality,
          ( left, and.getLeftSequentConnector, leftContext ) ::
            ( right, and.getRightSequentConnector, rightContext ) :: Nil
        )
        val newProof = AndRightRule(
          newLeftSubProof, leftConnector.child( aux1 ), newRightSubProof, rightConnector.child( aux2 )
        )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case or @ OrLeftRule( left, aux1, right, aux2 ) =>
        val context = equality.replacementContext
        val Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ) =
          splitEquality(
            equality,
            ( left, or.getLeftSequentConnector, context ) :: ( right, or.getRightSequentConnector, context ) :: Nil
          )
        val newProof = OrLeftRule( newLeftProof, leftConnector.child( aux1 ), newRightProof, rightConnector.child( aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case or @ OrRightRule( subProof, _, _ ) =>
        if ( or.mainIndices.head != equality.aux ) {
          val orConnector = or.getSequentConnector
          val newEquality = EqualityRightRule(
            subProof,
            orConnector.parent( equality.eq ),
            orConnector.parent( equality.aux ),
            equality.replacementContext
          )
          val newConnector = newEquality.getSequentConnector
          Some( OrRightRule( newEquality, newConnector.child( or.aux1 ), newConnector.child( or.aux2 ) ) )
        } else {
          val Abs( variable, Or( leftFormula, rightFormula ) ) = equality.replacementContext
          val newEquality1 = EqualityRightRule(
            subProof,
            or.getSequentConnector.parent( equality.eq ),
            or.getSequentConnector.parents( equality.aux ).head,
            Abs( variable, leftFormula )
          )
          val newEquality2 = EqualityRightRule(
            newEquality1,
            newEquality1.getSequentConnector.child( or.getSequentConnector.parent( equality.eq ) ),
            newEquality1.getSequentConnector.child( or.getSequentConnector.parents( equality.aux )( 1 ) ),
            Abs( variable, rightFormula )
          )
          val endConnector = newEquality2.getSequentConnector * newEquality1.getSequentConnector
          Some( OrRightRule( newEquality2, endConnector.child( or.aux1 ), endConnector.child( or.aux2 ) ) )
        }

      case imp @ ImpLeftRule( left, aux1, right, aux2 ) =>
        val context = equality.replacementContext
        val Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ) =
          splitEquality(
            equality,
            ( left, imp.getLeftSequentConnector, context ) :: ( right, imp.getRightSequentConnector, context ) :: Nil
          )
        val newProof = ImpLeftRule( newLeftProof, leftConnector.child( aux1 ), newRightProof, rightConnector.child( aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case imp @ ImpRightRule( subProof, _, _ ) =>
        if ( imp.mainIndices.head != equality.aux ) {
          val impConnector = imp.getSequentConnector
          val newEquality = EqualityRightRule(
            subProof, impConnector.parent( equality.eq ), impConnector.parent( equality.aux ), equality.replacementContext
          )
          val newConnector = newEquality.getSequentConnector
          Some( ImpRightRule( newEquality, newConnector.child( imp.aux1 ), newConnector.child( imp.aux2 ) ) )
        } else {
          val Abs( variable, Imp( leftFormula, rightFormula ) ) = equality.replacementContext
          val impConnector = imp.getSequentConnector
          val newEquality1 = EqualityLeftRule(
            subProof, impConnector.parent( equality.eq ), imp.aux1, Abs( variable, leftFormula )
          )
          val eq1Connector = newEquality1.getSequentConnector
          val newEquality2 = EqualityRightRule(
            newEquality1,
            eq1Connector.child( impConnector.parent( equality.eq ) ),
            eq1Connector.child( imp.aux2 ),
            Abs( variable, rightFormula )
          )
          val endConnector = newEquality2.getSequentConnector * eq1Connector
          Some( ImpRightRule( newEquality2, endConnector.child( imp.aux1 ), newEquality2.auxInConclusion ) )
        }

      case exists @ ExistsLeftRule( subProof, _, eigenVariable, quantifiedVariable ) =>
        val existsConnector = exists.getSequentConnector
        val newEquality = EqualityRightRule(
          subProof,
          existsConnector.parent( equality.eq ),
          existsConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( ExistsLeftRule(
          newEquality, newEquality.getSequentConnector.child( exists.aux ), eigenVariable, quantifiedVariable
        ) )

      case exists @ ExistsRightRule( _, _, _, _, _ ) =>
        val ( context, aFormula ) =
          if ( exists.mainIndices.head != equality.aux ) {
            ( equality.replacementContext, exists.A )
          } else {
            val Abs( variable, Ex( exVar, formula ) ) = equality.replacementContext
            val Ex( _, newAFormula ) = Substitution( variable, equality.by )( Ex( exVar, formula ) )
            ( instReplCtx( equality.replacementContext, exists.term ), newAFormula )
          }
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality,
          ( exists.subProof, exists.getSequentConnector, context ) :: Nil
        )
        Some( ExistsRightRule( newSubProof, subConnector.child( exists.aux ), aFormula, exists.term, exists.v ) )

      case forall @ ForallLeftRule( _, _, formula, term, variable ) =>
        val forallConnector = forall.getSequentConnector
        val newEquality = EqualityRightRule(
          forall.subProof,
          forallConnector.parent( equality.eq ),
          forallConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( ForallLeftRule(
          newEquality, newEquality.getSequentConnector.child( forall.aux ), formula, term, variable
        ) )

      case forall @ ForallRightRule( _, _, _, _ ) =>
        val context =
          if ( forall.mainIndices.head != equality.aux ) {
            equality.replacementContext
          } else {
            val Abs( oldVariable, all @ All( _, _ ) ) = equality.replacementContext
            val newReplVariable = rename( oldVariable, freeVariables( all ) + forall.eigenVariable )
            val All( _, formula ) = Substitution( oldVariable, newReplVariable )( all )
            Abs( newReplVariable, formula )
          }
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality,
          ( forall.subProof, forall.getSequentConnector, context ) :: Nil
        )
        Some( ForallRightRule(
          newSubProof, subConnector.child( forall.aux ), forall.eigenVariable, forall.quantifiedVariable
        ) )

      case eq @ EqualityLeftRule( _, _, _, _ ) =>
        // Fixme: Reduce depending on whether this inference is blocked by the same inference as eq
        None

      case eq @ EqualityRightRule( _, _, _, _ ) =>
        // Fixme: Reduce depending on whether this inference is blocked by the same inference as eq
        None

      case ind @ InductionRule( _, _, _ ) if ind.mainIndices.head != equality.aux =>
        val newSubProofs = splitEquality( equality, ind.cases.zip( ind.occConnectors ).map {
          case ( indCase, connector ) => ( indCase.proof, connector, equality.replacementContext )
        } ).zip( ind.cases )
        val newIndCases = newSubProofs.map {
          case ( ( subProof, connector ), indCase ) =>
            InductionCase(
              subProof,
              indCase.constructor,
              indCase.hypotheses.map( connector.child( _ ) ),
              indCase.eigenVars, connector.child( indCase.conclusion )
            )
        }
        val newProof = InductionRule( newIndCases, ind.formula, ind.term )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case _ => None
    }
  }
}

object equalityLeftReduction {

  /**
   * Tries to move the given equality inference upwards.
   * @param equality The equality inference to which the reduction is applied.
   * @return Either a reduced proof if the reduction could be applied, or None.
   */
  def apply( equality: EqualityLeftRule ): Option[LKProof] = {
    equality.subProof match {
      case weakening @ WeakeningLeftRule( _, _ ) if weakening.mainIndices.head == equality.eq =>
        None

      case weakening @ WeakeningLeftRule( _, _ ) =>
        val weakeningConnector = weakening.getSequentConnector
        if ( weakening.mainIndices.head == equality.aux ) {
          Some( WeakeningLeftRule( weakening.subProof, equality.conclusion( equality.auxInConclusion ) ) )
        } else {
          val newEqInf = EqualityLeftRule(
            weakening.subProof,
            weakeningConnector.parent( equality.eq ),
            weakeningConnector.parent( equality.aux ),
            equality.replacementContext
          )
          Some( WeakeningLeftRule( newEqInf, weakening.formula ) )
        }

      case weakening @ WeakeningRightRule( _, _ ) =>
        val newEqInf = EqualityLeftRule(
          weakening.subProof,
          weakening.getSequentConnector.parent( equality.eq ),
          weakening.getSequentConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( WeakeningRightRule( newEqInf, weakening.formula ) )

      case contraction @ ContractionLeftRule( _, _, _ ) =>
        val contractionConnector = contraction.getSequentConnector
        if ( contraction.mainIndices.head == equality.aux ) {
          val newEqInf1 = EqualityLeftRule(
            contraction.subProof,
            contractionConnector.parent( equality.eq ),
            contractionConnector.parents( equality.aux )( 0 ),
            equality.replacementContext
          )
          val newEqInf2 = EqualityLeftRule(
            newEqInf1,
            newEqInf1.getSequentConnector.child( contractionConnector.parent( equality.eq ) ),
            newEqInf1.getSequentConnector.child( contractionConnector.parents( equality.aux )( 1 ) ),
            equality.replacementContext
          )
          val endConnector = newEqInf2.getSequentConnector * newEqInf1.getSequentConnector
          Some( ContractionLeftRule(
            newEqInf2, endConnector.child( contraction.aux1 ), endConnector.child( contraction.aux2 )
          ) )
        } else {
          val newEqInf = EqualityLeftRule(
            contraction.subProof,
            contractionConnector.parents( equality.eq ).head,
            contractionConnector.parent( equality.aux ),
            equality.replacementContext
          )
          Some( ContractionLeftRule(
            newEqInf,
            newEqInf.getSequentConnector.child( contraction.aux1 ),
            newEqInf.getSequentConnector.child( contraction.aux2 )
          ) )
        }
      case contraction @ ContractionRightRule( _, _, _ ) =>
        val newEqInf = EqualityLeftRule(
          contraction.subProof,
          contraction.getSequentConnector.parent( equality.eq ),
          contraction.getSequentConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( ContractionRightRule(
          newEqInf,
          newEqInf.getSequentConnector.child( contraction.aux1 ),
          newEqInf.getSequentConnector.child( contraction.aux2 )
        ) )

      case negation @ NegLeftRule( _, _ ) =>
        val context = if ( negation.mainIndices.head == equality.aux ) {
          val Abs( variable, Neg( formula ) ) = equality.replacementContext
          Abs( variable, formula )
        } else {
          equality.replacementContext
        }
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality,
          ( negation.subProof, negation.getSequentConnector, context ) :: Nil
        )
        Some( NegLeftRule( newSubProof, subConnector.child( negation.aux ) ) )

      case negation @ NegRightRule( _, _ ) =>
        val newEqInf = EqualityLeftRule(
          negation.subProof,
          negation.getSequentConnector.parent( equality.eq ),
          negation.getSequentConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( NegRightRule( newEqInf, newEqInf.getSequentConnector.child( negation.aux ) ) )

      case or @ OrLeftRule( _, _, _, _ ) =>
        val ( leftContext, rightContext ) =
          if ( or.mainIndices.head == equality.aux ) {
            val Abs( variable, Or( lf, rf ) ) = equality.replacementContext
            ( Abs( variable, lf ), Abs( variable, rf ) )
          } else {
            ( equality.replacementContext, equality.replacementContext )
          }
        val Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ) = splitEquality(
          equality,
          ( or.leftSubProof, or.getLeftSequentConnector, leftContext ) ::
            ( or.rightSubProof, or.getRightSequentConnector, rightContext ) :: Nil
        )
        val newProof = OrLeftRule(
          newLeftProof, leftConnector.child( or.aux1 ), newRightProof, rightConnector.child( or.aux2 )
        )
        Some( ContractionMacroRule( newProof, or.conclusion, false ) )

      case or @ OrRightRule( _, _, _ ) =>
        val orConnector = or.getSequentConnector
        val newEqInf = EqualityLeftRule(
          or.subProof,
          orConnector.parent( equality.eq ),
          orConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( OrRightRule(
          newEqInf, newEqInf.getSequentConnector.child( or.aux1 ), newEqInf.getSequentConnector.child( or.aux2 )
        ) )

      case and @ AndLeftRule( _, _, _ ) =>
        val andConnector = and.getSequentConnector
        if ( and.mainIndices.head == equality.aux ) {
          val Abs( variable, And( leftFormula, rightFormula ) ) = equality.replacementContext
          val Seq( parentAuxL, parentAuxR ) = andConnector.parents( equality.aux )
          val newEqInf1 = EqualityLeftRule(
            and.subProof,
            andConnector.parent( equality.eq ),
            parentAuxL,
            Abs( variable, leftFormula )
          )
          val newEqInf2 = EqualityLeftRule(
            newEqInf1,
            newEqInf1.getSequentConnector.child( andConnector.parent( equality.eq ) ),
            newEqInf1.getSequentConnector.child( parentAuxR ),
            Abs( variable, rightFormula )
          )
          val endConnector = newEqInf2.getSequentConnector * newEqInf1.getSequentConnector
          Some( AndLeftRule( newEqInf2, endConnector.child( and.aux1 ), endConnector.child( and.aux2 ) ) )
        } else {
          val newEqInf = EqualityLeftRule(
            and.subProof,
            andConnector.parent( equality.eq ),
            andConnector.parent( equality.aux ),
            equality.replacementContext
          )
          Some( AndLeftRule(
            newEqInf, newEqInf.getSequentConnector.child( and.aux1 ), newEqInf.getSequentConnector.child( and.aux2 )
          ) )
        }
      case and @ AndRightRule( _, _, _, _ ) =>
        val context = equality.replacementContext
        val Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ) =
          splitEquality(
            equality,
            ( and.leftSubProof, and.getLeftSequentConnector, context ) ::
              ( and.rightSubProof, and.getRightSequentConnector, context ) :: Nil
          )
        val newProof = AndRightRule(
          newLeftProof, leftConnector.child( and.aux1 ), newRightProof, rightConnector.child( and.aux2 )
        )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case imp @ ImpLeftRule( _, _, _, _ ) =>
        val impLeftConnector = imp.getLeftSequentConnector
        val impRightConnector = imp.getRightSequentConnector
        val ( leftContext, rightContext ) =
          if ( imp.mainIndices.head == equality.aux ) {
            val Abs( variable, Imp( leftFormula, rightFormula ) ) = equality.replacementContext
            ( Abs( variable, leftFormula ), Abs( variable, rightFormula ) )
          } else {
            ( equality.replacementContext, equality.replacementContext )
          }
        val Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ) =
          splitEquality(
            equality,
            ( imp.leftSubProof, impLeftConnector, leftContext ) ::
              ( imp.rightSubProof, impRightConnector, rightContext ) :: Nil
          )
        val newProof = ImpLeftRule(
          newLeftProof, leftConnector.child( imp.aux1 ), newRightProof, rightConnector.child( imp.aux2 )
        )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case imp @ ImpRightRule( _, _, _ ) =>
        val newEqInf = EqualityLeftRule(
          imp.subProof,
          imp.getSequentConnector.parent( equality.eq ),
          imp.getSequentConnector.parent( equality.aux ),
          equality.replacementContext
        )
        Some( ImpRightRule(
          newEqInf, newEqInf.getSequentConnector.child( imp.aux1 ), newEqInf.getSequentConnector.child( imp.aux2 )
        ) )

      case exists @ ExistsLeftRule( _, _, _, _ ) =>
        val context =
          if ( exists.mainIndices.head == equality.aux ) {
            val Abs( oldVariable, ex @ Ex( _, _ ) ) = equality.replacementContext
            val newReplVariable = rename( oldVariable, freeVariables( ex ) + exists.eigenVariable )
            val Ex( _, formula ) = Substitution( oldVariable, newReplVariable )( ex )
            Abs( newReplVariable, formula )
          } else {
            equality.replacementContext
          }
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality, ( exists.subProof, exists.getSequentConnector, context ) :: Nil
        )
        Some( ExistsLeftRule(
          newSubProof, subConnector.child( exists.aux ), exists.eigenVariable, exists.quantifiedVariable
        ) )

      case exists @ ExistsRightRule( _, _, _, _, _ ) =>
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality, ( exists.subProof, exists.getSequentConnector, equality.replacementContext ) :: Nil
        )
        Some( ExistsRightRule( newSubProof, subConnector.child( exists.aux ), exists.A, exists.term, exists.v ) )

      case all @ ForallLeftRule( _, _, _, _, _ ) =>
        val ( context, aFormula ) = if ( all.mainIndices.head == equality.aux ) {
          val Abs( variable, All( allVar, formula ) ) = equality.replacementContext
          val newContext = instReplCtx( equality.replacementContext, all.term )
          val All( _, newAFormula ) = Substitution( variable, equality.by )( All( allVar, formula ) )
          ( newContext, newAFormula )
        } else {
          ( equality.replacementContext, all.A )
        }
        val Seq( ( newSubProof, subConnector ) ) = splitEquality(
          equality, ( all.subProof, all.getSequentConnector, context ) :: Nil
        )
        Some( ForallLeftRule( newSubProof, subConnector.child( all.aux ), aFormula, all.term, all.v ) )

      case all @ ForallRightRule( _, _, _, _ ) =>
        val Seq( ( newSubProof, newConnector ) ) = splitEquality(
          equality, ( all.subProof, all.getSequentConnector, equality.replacementContext ) :: Nil
        )
        Some( ForallRightRule( newSubProof, newConnector.child( all.aux ), all.eigenVariable, all.quantifiedVariable ) )

      case eq @ EqualityLeftRule( _, _, _, _ ) =>
        // Fixme: Reduce depending on whether this inference is blocked by the same inference as eq
        None

      case eq @ EqualityRightRule( _, _, _, _ ) =>
        // Fixme: Reduce depending on whether this inference is blocked by the same inference as eq
        None

      case ind @ InductionRule( _, _, _ ) =>
        val newSubProofs = splitEquality( equality, ind.cases.zip( ind.occConnectors ).map {
          case ( indCase, connector ) => ( indCase.proof, connector, equality.replacementContext )
        } ).zip( ind.cases )
        val newIndCases = newSubProofs.map {
          case ( ( subProof, connector ), indCase ) =>
            InductionCase(
              subProof,
              indCase.constructor,
              indCase.hypotheses.map( connector.child( _ ) ),
              indCase.eigenVars, connector.child( indCase.conclusion )
            )
        }
        val newProof = InductionRule( newIndCases, ind.formula, ind.term )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case cut @ CutRule( _, _, _, _ ) =>
        val context = equality.replacementContext
        val Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ) =
          splitEquality(
            equality,
            ( cut.leftSubProof, cut.getLeftSequentConnector, context ) ::
              ( cut.rightSubProof, cut.getRightSequentConnector, context ) :: Nil
          )
        val newProof = CutRule(
          newLeftProof, leftConnector.child( cut.aux1 ), newRightProof, rightConnector.child( cut.aux2 )
        )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ) )

      case _ => None
    }
  }
}

object splitEquality {

  def apply( equality: EqualityRule, subProofs: Seq[( LKProof, SequentConnector, Abs )] ): Seq[( LKProof, SequentConnector )] = {
    for {
      ( subProof, connector, replacementContext ) <- subProofs
    } yield {
      if ( connector.parents( equality.aux ).nonEmpty ) insertEquality( equality, subProof, connector, replacementContext )
      else ( subProof, SequentConnector( subProof.conclusion ) )
    }
  }

  def insertEquality( equality: EqualityRule, subProof: LKProof, connector: SequentConnector, replacementContext: Abs ): ( LKProof, SequentConnector ) = {
    if ( connector.parents( equality.eq ) == Seq() ) {
      val newSubProof = WeakeningLeftRule( subProof, equality.equation )
      val ( newProof, newProofConnector ) = createEquality(
        newSubProof,
        newSubProof.mainIndices.head,
        newSubProof.getSequentConnector.child( connector.parent( equality.aux ) ),
        replacementContext
      )
      ( newProof, newProofConnector * newSubProof.getSequentConnector )
    } else {
      createEquality(
        subProof,
        connector.parent( equality.eq ),
        connector.parent( equality.aux ),
        replacementContext
      )
    }
  }

  private def createEquality(
    subProof: LKProof, equation: SequentIndex, auxiliary: SequentIndex, replacementContext: Abs
  ): ( LKProof, SequentConnector ) =
    auxiliary match {
      case Suc( _ ) =>
        val equalityInference = EqualityRightRule( subProof, equation, auxiliary, replacementContext )
        ( equalityInference, equalityInference.getSequentConnector )
      case Ant( _ ) =>
        val equalityInference = EqualityLeftRule( subProof, equation, auxiliary, replacementContext )
        ( equalityInference, equalityInference.getSequentConnector )
    }
}

/**
 * Instantiates the quantifier inside a replacement context.
 *
 * Given λx ∀y P(x,y) and f(c), it will return λx P(x,f(c)).
 */
private object instReplCtx {
  def apply( ctx: Abs, term: Expr ): Abs =
    ctx match {
      case Abs( x, quantFormula ) if freeVariables( term ) contains x =>
        val newX = rename( x, freeVariables( term ) )
        instReplCtx( Abs( newX, Substitution( x -> newX )( quantFormula ) ), term )
      case Abs( x, quantFormula: Formula ) =>
        Abs( x, instantiate( quantFormula, term ) )
    }
}
