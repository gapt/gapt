package gapt.proofs.lk.transformations

import gapt.expr.Abs
import gapt.expr.All
import gapt.expr.And
import gapt.expr.Ex
import gapt.expr.Imp
import gapt.expr.Neg
import gapt.expr.Or
import gapt.expr.Substitution
import gapt.expr.freeVariables
import gapt.expr.rename
import gapt.proofs.Ant
import gapt.proofs.SequentConnector
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.expansion.instReplCtx
import gapt.proofs.guessPermutation
import gapt.proofs.lk.AndLeftRule
import gapt.proofs.lk.AndRightRule
import gapt.proofs.lk.ContractionLeftRule
import gapt.proofs.lk.ContractionMacroRule
import gapt.proofs.lk.ContractionRightRule
import gapt.proofs.lk.CutRule
import gapt.proofs.lk.EqualityLeftRule
import gapt.proofs.lk.EqualityRightRule
import gapt.proofs.lk.EqualityRule
import gapt.proofs.lk.ExistsLeftRule
import gapt.proofs.lk.ExistsRightRule
import gapt.proofs.lk.ForallLeftRule
import gapt.proofs.lk.ForallRightRule
import gapt.proofs.lk.ImpLeftRule
import gapt.proofs.lk.ImpRightRule
import gapt.proofs.lk.InductionCase
import gapt.proofs.lk.InductionRule
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.NegLeftRule
import gapt.proofs.lk.NegRightRule
import gapt.proofs.lk.OrLeftRule
import gapt.proofs.lk.OrRightRule
import gapt.proofs.lk.WeakeningLeftRule
import gapt.proofs.lk.WeakeningRightRule
import gapt.proofs.lk.transformations

object pushEqualityInferencesToLeaves {

  /**
   * Pushes equality inferences to the leaves.
   *
   * @param proof The proof to which this transformation is applied
   * @return A proof of the same end-sequent which is obtained from the given proof
   *        by moving all equality inferences towards the leaves as far as possible. Weakening inferences are moved
   *        as close to the root as possible.
   */
  def apply( proof: LKProof ): LKProof = {
    cleanStructuralRules( visitor( proof, () ), false )
  }

  private object visitor extends LKVisitor[Unit] {

    override protected def recurse( proof: LKProof, arg: Unit ) = {
      proof match {
        case EqualityLeftRule( weakening @ WeakeningLeftRule( _, _ ), _, _, _ ) if weakeningOnlySubTree( weakening ) =>
          ( proof, SequentConnector( proof.conclusion ) )

        case EqualityLeftRule( weakening @ WeakeningRightRule( _, _ ), _, _, _ ) if weakeningOnlySubTree( weakening ) =>
          ( proof, SequentConnector( proof.conclusion ) )

        case EqualityRightRule( weakening @ WeakeningLeftRule( _, _ ), _, _, _ ) if weakeningOnlySubTree( weakening ) =>
          ( proof, SequentConnector( proof.conclusion ) )

        case EqualityRightRule( weakening @ WeakeningRightRule( _, _ ), _, _, _ ) if weakeningOnlySubTree( weakening ) =>
          ( proof, SequentConnector( proof.conclusion ) )

        case equality @ EqualityLeftRule( weakening @ WeakeningLeftRule( _, _ ), _, _, _ ) if weakening.mainIndices.head == equality.eq =>
          val ( newSubProof, connector ) = pushSingleWeakeningToLeaves.withConnector( weakening )
          val ( newProof, _ ) = recurse( EqualityLeftRule( newSubProof, connector.child( equality.eq ), connector.child( equality.aux ), equality.replacementContext ), () )
          ( newProof, SequentConnector.guessInjection( proof.conclusion, newProof.conclusion ).inv )

        case equality @ EqualityRightRule( weakening @ WeakeningLeftRule( _, _ ), _, _, _ ) if weakening.mainIndices.head == equality.eq =>
          val ( newSubProof, connector ) = pushSingleWeakeningToLeaves.withConnector( weakening )
          val ( newProof, _ ) = recurse( EqualityRightRule( newSubProof, connector.child( equality.eq ), connector.child( equality.aux ), equality.replacementContext ), () )
          ( newProof, SequentConnector.guessInjection( proof.conclusion, newProof.conclusion ).inv )

        case EqualityLeftRule( _, _, _, _ ) | EqualityRightRule( _, _, _, _ ) =>
          val ( reducedProof, connector ) = super.recurse( proof, () )
          equalityReduction( reducedProof ) match {
            case Some( ( newProof, _, _ ) ) =>
              val ( finalProof, _ ) = super.recurse( newProof, () )
              ( finalProof, SequentConnector.guessInjection( proof.conclusion, finalProof.conclusion ).inv )
            case None => ( reducedProof, connector )
          }
        case _ => super.recurse( proof, () )
      }
    }
  }

  private def equalityReduction( proof: LKProof ): Option[( LKProof, SequentConnector, Boolean )] = proof match {
    case eq @ EqualityLeftRule( _, _, _, _ ) =>
      equalityLeftReduction( eq ) map {
        case ( newProof, weakeningIntro ) =>
          val ( _, connector ) = guessPermutation( proof, newProof )
          ( newProof, connector, weakeningIntro )
      }
    case eq @ EqualityRightRule( _, _, _, _ ) =>
      equalityRightReduction( eq ).map {
        case ( newProof, weakeningIntro ) =>
          val ( _, connector ) = guessPermutation( proof, newProof )
          ( newProof, connector, weakeningIntro )
      }
    case _ => None
  }
}

object equalityRightReduction {

  /**
   * Tries to move the given equality inference upwards.
   * @param equality The equality inference to which the reduction is applied.
   * @return Either a reduced proof if the reduction could be applied, or None.
   */
  def apply( equality: EqualityRightRule ): Option[( LKProof, Boolean )] = {
    equality.subProof match {

      case weakening @ WeakeningLeftRule( subProof, _ ) if weakening.mainIndices.head != equality.eq =>
        val connector = weakening.getSequentConnector
        val newEquality = new EqualityRightRule(
          subProof,
          connector.parent( equality.eq ),
          connector.parent( equality.aux ),
          equality.replacementContext )
        Some( WeakeningLeftRule( newEquality, weakening.formula ), false )

      case weakening @ WeakeningRightRule( subProof, _ ) =>
        if ( weakening.mainIndices.head == equality.aux ) {
          Some( WeakeningRightRule( subProof, equality.mainFormula ), false )
        } else {
          val connector = weakening.getSequentConnector
          val newEquality = new EqualityRightRule(
            subProof,
            connector.parent( equality.eq ),
            connector.parent( equality.aux ),
            equality.replacementContext )
          Some( WeakeningRightRule( newEquality, weakening.formula ), false )
        }

      case contraction @ ContractionLeftRule( subProof, _, _ ) =>
        val connector = contraction.getSequentConnector
        val newEquality = EqualityRightRule(
          subProof,
          connector.parents( equality.eq ).head,
          connector.parent( equality.aux ),
          equality.replacementContext )
        val connector2 = newEquality.getSequentConnector
        Some( ContractionLeftRule( newEquality, connector2.child( contraction.aux1 ), connector2.child( contraction.aux2 ) ), false )

      case contraction @ ContractionRightRule( _, _, _ ) =>
        val contractionConnector = contraction.getSequentConnector
        if ( contraction.mainIndices.head != equality.aux ) {
          val newEquality = EqualityRightRule(
            contraction.subProof,
            contractionConnector.parent( equality.eq ),
            contractionConnector.parent( equality.aux ),
            equality.replacementContext )
          Some( ContractionRightRule(
            newEquality,
            newEquality.getSequentConnector.child( contraction.aux1 ),
            newEquality.getSequentConnector.child( contraction.aux2 ) ), false )
        } else {
          val newEquality1 = EqualityRightRule(
            contraction.subProof,
            contractionConnector.parent( equality.eq ),
            contractionConnector.parents( equality.aux )( 0 ),
            equality.replacementContext )
          val equalityConnector = newEquality1.getSequentConnector
          val newEquality2 = EqualityRightRule(
            newEquality1,
            equalityConnector.child( contractionConnector.parent( equality.eq ) ),
            equalityConnector.child( contractionConnector.parents( equality.aux )( 1 ) ),
            equality.replacementContext )
          val endConnector = newEquality2.getSequentConnector * equalityConnector
          Some( ContractionRightRule(
            newEquality2,
            endConnector.child( contraction.aux1 ),
            endConnector.child( contraction.aux2 ) ), false )
        }

      case cut @ CutRule( _, _, _, _ ) =>
        val ( Seq( ( newLeftSubProof, leftConnector ), ( newRightSubProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( cut.leftSubProof, cut.getLeftSequentConnector, equality.replacementContext ) ::
              ( cut.rightSubProof, cut.getRightSequentConnector, equality.replacementContext ) :: Nil )
        val newSubProof = CutRule(
          newLeftSubProof, leftConnector.child( cut.aux1 ), newRightSubProof, rightConnector.child( cut.aux2 ) )
        Some( ContractionMacroRule( newSubProof, equality.conclusion, false ), weakeningIntro )

      case neg @ NegLeftRule( _, _ ) =>
        val negConnector = neg.getSequentConnector
        val newEquality = EqualityRightRule(
          neg.subProof,
          negConnector.parent( equality.eq ),
          negConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( NegLeftRule( newEquality, newEquality.getSequentConnector.child( neg.aux ) ), false )

      case neg @ NegRightRule( _, _ ) =>
        val context =
          if ( neg.mainIndices.head != equality.aux ) {
            equality.replacementContext
          } else {
            val Abs( variable, Neg( formula ) ) = equality.replacementContext
            Abs( variable, formula )
          }
        val ( Seq( ( newSubProof, subConnector ) ), weakeningIntro ) = transformations.splitEquality(
          equality, ( neg.subProof, neg.getSequentConnector, context ) :: Nil )
        Some( NegRightRule( newSubProof, subConnector.child( neg.aux ) ), weakeningIntro )

      case and @ AndLeftRule( _, _, _ ) =>
        val andConnector = and.getSequentConnector
        val newEquality = EqualityRightRule(
          and.subProof,
          andConnector.parent( equality.eq ),
          andConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( AndLeftRule(
          newEquality,
          newEquality.getSequentConnector.child( and.aux1 ),
          newEquality.getSequentConnector.child( and.aux2 ) ), false )

      case and @ AndRightRule( left, aux1, right, aux2 ) =>
        val ( leftContext, rightContext ) =
          if ( and.mainIndices.head != equality.aux ) {
            ( equality.replacementContext, equality.replacementContext )
          } else {
            val Abs( variable, And( leftFormula, rightFormula ) ) = equality.replacementContext
            ( Abs( variable, leftFormula ), Abs( variable, rightFormula ) )
          }
        val ( Seq( ( newLeftSubProof, leftConnector ), ( newRightSubProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( left, and.getLeftSequentConnector, leftContext ) ::
              ( right, and.getRightSequentConnector, rightContext ) :: Nil )
        val newProof = AndRightRule(
          newLeftSubProof, leftConnector.child( aux1 ), newRightSubProof, rightConnector.child( aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

      case or @ OrLeftRule( left, aux1, right, aux2 ) =>
        val context = equality.replacementContext
        val ( Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( left, or.getLeftSequentConnector, context ) :: ( right, or.getRightSequentConnector, context ) :: Nil )
        val newProof = OrLeftRule( newLeftProof, leftConnector.child( aux1 ), newRightProof, rightConnector.child( aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

      case or @ OrRightRule( subProof, _, _ ) =>
        if ( or.mainIndices.head != equality.aux ) {
          val orConnector = or.getSequentConnector
          val newEquality = EqualityRightRule(
            subProof,
            orConnector.parent( equality.eq ),
            orConnector.parent( equality.aux ),
            equality.replacementContext )
          val newConnector = newEquality.getSequentConnector
          Some( OrRightRule( newEquality, newConnector.child( or.aux1 ), newConnector.child( or.aux2 ) ), false )
        } else {
          val Abs( variable, Or( leftFormula, rightFormula ) ) = equality.replacementContext
          val newEquality1 = EqualityRightRule(
            subProof,
            or.getSequentConnector.parent( equality.eq ),
            or.getSequentConnector.parents( equality.aux ).head,
            Abs( variable, leftFormula ) )
          val newEquality2 = EqualityRightRule(
            newEquality1,
            newEquality1.getSequentConnector.child( or.getSequentConnector.parent( equality.eq ) ),
            newEquality1.getSequentConnector.child( or.getSequentConnector.parents( equality.aux )( 1 ) ),
            Abs( variable, rightFormula ) )
          val endConnector = newEquality2.getSequentConnector * newEquality1.getSequentConnector
          Some( OrRightRule( newEquality2, endConnector.child( or.aux1 ), endConnector.child( or.aux2 ) ), false )
        }

      case imp @ ImpLeftRule( left, aux1, right, aux2 ) =>
        val context = equality.replacementContext
        val ( Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( left, imp.getLeftSequentConnector, context ) :: ( right, imp.getRightSequentConnector, context ) :: Nil )
        val newProof = ImpLeftRule( newLeftProof, leftConnector.child( aux1 ), newRightProof, rightConnector.child( aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

      case imp @ ImpRightRule( subProof, _, _ ) =>
        if ( imp.mainIndices.head != equality.aux ) {
          val impConnector = imp.getSequentConnector
          val newEquality = EqualityRightRule(
            subProof, impConnector.parent( equality.eq ), impConnector.parent( equality.aux ), equality.replacementContext )
          val newConnector = newEquality.getSequentConnector
          Some( ImpRightRule( newEquality, newConnector.child( imp.aux1 ), newConnector.child( imp.aux2 ) ), false )
        } else {
          val Abs( variable, Imp( leftFormula, rightFormula ) ) = equality.replacementContext
          val impConnector = imp.getSequentConnector
          val newEquality1 = EqualityLeftRule(
            subProof, impConnector.parent( equality.eq ), imp.aux1, Abs( variable, leftFormula ) )
          val eq1Connector = newEquality1.getSequentConnector
          val newEquality2 = EqualityRightRule(
            newEquality1,
            eq1Connector.child( impConnector.parent( equality.eq ) ),
            eq1Connector.child( imp.aux2 ),
            Abs( variable, rightFormula ) )
          val endConnector = newEquality2.getSequentConnector * eq1Connector
          Some( ImpRightRule( newEquality2, endConnector.child( imp.aux1 ), newEquality2.auxInConclusion ), false )
        }

      case exists @ ExistsLeftRule( subProof, _, eigenVariable, quantifiedVariable ) =>
        val existsConnector = exists.getSequentConnector
        val newEquality = EqualityRightRule(
          subProof,
          existsConnector.parent( equality.eq ),
          existsConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( ExistsLeftRule(
          newEquality, newEquality.getSequentConnector.child( exists.aux ), eigenVariable, quantifiedVariable ), false )

      case exists @ ExistsRightRule( _, _, _, _, _ ) =>
        val ( context, aFormula ) =
          if ( exists.mainIndices.head != equality.aux ) {
            ( equality.replacementContext, exists.A )
          } else {
            val Abs( variable, Ex( exVar, formula ) ) = equality.replacementContext
            val Ex( _, newAFormula ) = Substitution( variable, equality.by )( Ex( exVar, formula ) )
            ( instReplCtx( equality.replacementContext, exists.term ), newAFormula )
          }
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( exists.subProof, exists.getSequentConnector, context ) :: Nil )
        Some( ExistsRightRule( newSubProof, subConnector.child( exists.aux ), aFormula, exists.term, exists.v ), false )

      case forall @ ForallLeftRule( _, _, formula, term, variable ) =>
        val forallConnector = forall.getSequentConnector
        val newEquality = EqualityRightRule(
          forall.subProof,
          forallConnector.parent( equality.eq ),
          forallConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( ForallLeftRule(
          newEquality, newEquality.getSequentConnector.child( forall.aux ), formula, term, variable ), false )

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
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( forall.subProof, forall.getSequentConnector, context ) :: Nil )
        Some( ForallRightRule(
          newSubProof, subConnector.child( forall.aux ), forall.eigenVariable, forall.quantifiedVariable ), false )

      case eq @ EqualityLeftRule( _, _, _, _ ) if eq.mainIndices.head != equality.eq =>
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( eq.subProof, eq.getSequentConnector, equality.replacementContext ) :: Nil )
        val newProof = EqualityLeftRule(
          newSubProof,
          subConnector.child( eq.eq ),
          subConnector.child( eq.aux ),
          eq.replacementContext )
        Some( newProof, false )

      case eq @ EqualityRightRule( _, _, _, _ ) if eq.mainIndices.head != equality.aux =>
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( eq.subProof, eq.getSequentConnector, equality.replacementContext ) :: Nil )
        val newProof = EqualityRightRule(
          newSubProof,
          subConnector.child( eq.eq ),
          subConnector.child( eq.aux ),
          eq.replacementContext )
        Some( newProof, false )

      case ind @ InductionRule( _, _, _ ) if ind.mainIndices.head != equality.aux =>
        val ( splitCases, weakeningIntro ) = splitEquality( equality, ind.cases.zip( ind.occConnectors ).map {
          case ( indCase, connector ) => ( indCase.proof, connector, equality.replacementContext )
        } )
        val newSubProofs = splitCases.zip( ind.cases )
        val newIndCases = newSubProofs.map {
          case ( ( subProof, connector ), indCase ) =>
            InductionCase(
              subProof,
              indCase.constructor,
              indCase.hypotheses.map( connector.child ),
              indCase.eigenVars, connector.child( indCase.conclusion ) )
        }
        val newProof = InductionRule( newIndCases, ind.formula, ind.term )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

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
  def apply( equality: EqualityLeftRule ): Option[( LKProof, Boolean )] = {
    equality.subProof match {
      case weakening @ WeakeningLeftRule( _, _ ) if weakening.mainIndices.head == equality.eq =>
        None

      case weakening @ WeakeningLeftRule( _, _ ) =>
        val weakeningConnector = weakening.getSequentConnector
        if ( weakening.mainIndices.head == equality.aux ) {
          Some( WeakeningLeftRule( weakening.subProof, equality.conclusion( equality.auxInConclusion ) ), false )
        } else {
          val newEqInf = EqualityLeftRule(
            weakening.subProof,
            weakeningConnector.parent( equality.eq ),
            weakeningConnector.parent( equality.aux ),
            equality.replacementContext )
          Some( WeakeningLeftRule( newEqInf, weakening.formula ), false )
        }

      case weakening @ WeakeningRightRule( _, _ ) =>
        val newEqInf = EqualityLeftRule(
          weakening.subProof,
          weakening.getSequentConnector.parent( equality.eq ),
          weakening.getSequentConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( WeakeningRightRule( newEqInf, weakening.formula ), false )

      case contraction @ ContractionLeftRule( _, _, _ ) =>
        val contractionConnector = contraction.getSequentConnector
        if ( contraction.mainIndices.head == equality.aux ) {
          val newEqInf1 = EqualityLeftRule(
            contraction.subProof,
            contractionConnector.parent( equality.eq ),
            contractionConnector.parents( equality.aux )( 0 ),
            equality.replacementContext )
          val newEqInf2 = EqualityLeftRule(
            newEqInf1,
            newEqInf1.getSequentConnector.child( contractionConnector.parent( equality.eq ) ),
            newEqInf1.getSequentConnector.child( contractionConnector.parents( equality.aux )( 1 ) ),
            equality.replacementContext )
          val endConnector = newEqInf2.getSequentConnector * newEqInf1.getSequentConnector
          Some( ContractionLeftRule(
            newEqInf2, endConnector.child( contraction.aux1 ), endConnector.child( contraction.aux2 ) ), false )
        } else {
          val newEqInf = EqualityLeftRule(
            contraction.subProof,
            contractionConnector.parents( equality.eq ).head,
            contractionConnector.parent( equality.aux ),
            equality.replacementContext )
          Some( ContractionLeftRule(
            newEqInf,
            newEqInf.getSequentConnector.child( contraction.aux1 ),
            newEqInf.getSequentConnector.child( contraction.aux2 ) ), false )
        }
      case contraction @ ContractionRightRule( _, _, _ ) =>
        val newEqInf = EqualityLeftRule(
          contraction.subProof,
          contraction.getSequentConnector.parent( equality.eq ),
          contraction.getSequentConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( ContractionRightRule(
          newEqInf,
          newEqInf.getSequentConnector.child( contraction.aux1 ),
          newEqInf.getSequentConnector.child( contraction.aux2 ) ), false )

      case negation @ NegLeftRule( _, _ ) =>
        val context = if ( negation.mainIndices.head == equality.aux ) {
          val Abs( variable, Neg( formula ) ) = equality.replacementContext
          Abs( variable, formula )
        } else {
          equality.replacementContext
        }
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( negation.subProof, negation.getSequentConnector, context ) :: Nil )
        Some( NegLeftRule( newSubProof, subConnector.child( negation.aux ) ), false )

      case negation @ NegRightRule( _, _ ) =>
        val newEqInf = EqualityLeftRule(
          negation.subProof,
          negation.getSequentConnector.parent( equality.eq ),
          negation.getSequentConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( NegRightRule( newEqInf, newEqInf.getSequentConnector.child( negation.aux ) ), false )

      case or @ OrLeftRule( _, _, _, _ ) =>
        val ( leftContext, rightContext ) =
          if ( or.mainIndices.head == equality.aux ) {
            val Abs( variable, Or( lf, rf ) ) = equality.replacementContext
            ( Abs( variable, lf ), Abs( variable, rf ) )
          } else {
            ( equality.replacementContext, equality.replacementContext )
          }
        val ( Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( or.leftSubProof, or.getLeftSequentConnector, leftContext ) ::
              ( or.rightSubProof, or.getRightSequentConnector, rightContext ) :: Nil )
        val newProof = OrLeftRule(
          newLeftProof, leftConnector.child( or.aux1 ), newRightProof, rightConnector.child( or.aux2 ) )
        Some( ContractionMacroRule( newProof, or.conclusion, false ), weakeningIntro )

      case or @ OrRightRule( _, _, _ ) =>
        val orConnector = or.getSequentConnector
        val newEqInf = EqualityLeftRule(
          or.subProof,
          orConnector.parent( equality.eq ),
          orConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( OrRightRule(
          newEqInf, newEqInf.getSequentConnector.child( or.aux1 ), newEqInf.getSequentConnector.child( or.aux2 ) ), false )

      case and @ AndLeftRule( _, _, _ ) =>
        val andConnector = and.getSequentConnector
        if ( and.mainIndices.head == equality.aux ) {
          val Abs( variable, And( leftFormula, rightFormula ) ) = equality.replacementContext
          val Seq( parentAuxL, parentAuxR ) = andConnector.parents( equality.aux )
          val newEqInf1 = EqualityLeftRule(
            and.subProof,
            andConnector.parent( equality.eq ),
            parentAuxL,
            Abs( variable, leftFormula ) )
          val newEqInf2 = EqualityLeftRule(
            newEqInf1,
            newEqInf1.getSequentConnector.child( andConnector.parent( equality.eq ) ),
            newEqInf1.getSequentConnector.child( parentAuxR ),
            Abs( variable, rightFormula ) )
          val endConnector = newEqInf2.getSequentConnector * newEqInf1.getSequentConnector
          Some( AndLeftRule( newEqInf2, endConnector.child( and.aux1 ), endConnector.child( and.aux2 ) ), false )
        } else {
          val newEqInf = EqualityLeftRule(
            and.subProof,
            andConnector.parent( equality.eq ),
            andConnector.parent( equality.aux ),
            equality.replacementContext )
          Some( AndLeftRule(
            newEqInf, newEqInf.getSequentConnector.child( and.aux1 ), newEqInf.getSequentConnector.child( and.aux2 ) ), false )
        }
      case and @ AndRightRule( _, _, _, _ ) =>
        val context = equality.replacementContext
        val ( Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( and.leftSubProof, and.getLeftSequentConnector, context ) ::
              ( and.rightSubProof, and.getRightSequentConnector, context ) :: Nil )
        val newProof = AndRightRule(
          newLeftProof, leftConnector.child( and.aux1 ), newRightProof, rightConnector.child( and.aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

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
        val ( Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( imp.leftSubProof, impLeftConnector, leftContext ) ::
              ( imp.rightSubProof, impRightConnector, rightContext ) :: Nil )
        val newProof = ImpLeftRule(
          newLeftProof, leftConnector.child( imp.aux1 ), newRightProof, rightConnector.child( imp.aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

      case imp @ ImpRightRule( _, _, _ ) =>
        val newEqInf = EqualityLeftRule(
          imp.subProof,
          imp.getSequentConnector.parent( equality.eq ),
          imp.getSequentConnector.parent( equality.aux ),
          equality.replacementContext )
        Some( ImpRightRule(
          newEqInf, newEqInf.getSequentConnector.child( imp.aux1 ), newEqInf.getSequentConnector.child( imp.aux2 ) ), false )

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
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality, ( exists.subProof, exists.getSequentConnector, context ) :: Nil )
        Some( ExistsLeftRule(
          newSubProof, subConnector.child( exists.aux ), exists.eigenVariable, exists.quantifiedVariable ), false )

      case exists @ ExistsRightRule( _, _, _, _, _ ) =>
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality, ( exists.subProof, exists.getSequentConnector, equality.replacementContext ) :: Nil )
        Some( ExistsRightRule( newSubProof, subConnector.child( exists.aux ), exists.A, exists.term, exists.v ), false )

      case all @ ForallLeftRule( _, _, _, _, _ ) =>
        val ( context, aFormula ) = if ( all.mainIndices.head == equality.aux ) {
          val Abs( variable, All( allVar, formula ) ) = equality.replacementContext
          val newContext = instReplCtx( equality.replacementContext, all.term )
          val All( _, newAFormula ) = Substitution( variable, equality.by )( All( allVar, formula ) )
          ( newContext, newAFormula )
        } else {
          ( equality.replacementContext, all.A )
        }
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality, ( all.subProof, all.getSequentConnector, context ) :: Nil )
        Some( ForallLeftRule( newSubProof, subConnector.child( all.aux ), aFormula, all.term, all.v ), false )

      case all @ ForallRightRule( _, _, _, _ ) =>
        val ( Seq( ( newSubProof, newConnector ) ), _ ) = transformations.splitEquality(
          equality, ( all.subProof, all.getSequentConnector, equality.replacementContext ) :: Nil )
        Some( ForallRightRule(
          newSubProof, newConnector.child( all.aux ), all.eigenVariable, all.quantifiedVariable ), false )

      case eq @ EqualityLeftRule( _, _, _, _ ) if eq.mainIndices.head != equality.aux && eq.mainIndices.head != equality.eq && eq.eqInConclusion != equality.aux =>
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( eq.subProof, eq.getSequentConnector, equality.replacementContext ) :: Nil )
        val newProof = EqualityLeftRule(
          newSubProof,
          subConnector.child( eq.eq ),
          subConnector.child( eq.aux ),
          eq.replacementContext )
        Some( newProof, false )

      case eq @ EqualityRightRule( _, _, _, _ ) if equality.aux != eq.eqInConclusion =>
        val ( Seq( ( newSubProof, subConnector ) ), _ ) = transformations.splitEquality(
          equality,
          ( eq.subProof, eq.getSequentConnector, equality.replacementContext ) :: Nil )
        val newProof = EqualityRightRule(
          newSubProof,
          subConnector.child( eq.eq ),
          subConnector.child( eq.aux ),
          eq.replacementContext )
        Some( newProof, false )

      case ind @ InductionRule( _, _, _ ) =>
        val ( splitCases, weakeningIntro ) = splitEquality( equality, ind.cases.zip( ind.occConnectors ).map {
          case ( indCase, connector ) => ( indCase.proof, connector, equality.replacementContext )
        } )
        val newSubProofs = splitCases.zip( ind.cases )
        val newIndCases = newSubProofs.map {
          case ( ( subProof, connector ), indCase ) =>
            InductionCase(
              subProof,
              indCase.constructor,
              indCase.hypotheses.map( connector.child ),
              indCase.eigenVars, connector.child( indCase.conclusion ) )
        }
        val newProof = InductionRule( newIndCases, ind.formula, ind.term )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

      case cut @ CutRule( _, _, _, _ ) =>
        val context = equality.replacementContext
        val ( Seq( ( newLeftProof, leftConnector ), ( newRightProof, rightConnector ) ), weakeningIntro ) =
          transformations.splitEquality(
            equality,
            ( cut.leftSubProof, cut.getLeftSequentConnector, context ) ::
              ( cut.rightSubProof, cut.getRightSequentConnector, context ) :: Nil )
        val newProof = CutRule(
          newLeftProof, leftConnector.child( cut.aux1 ), newRightProof, rightConnector.child( cut.aux2 ) )
        Some( ContractionMacroRule( newProof, equality.conclusion, false ), weakeningIntro )

      case _ => None
    }
  }
}

private object splitEquality {

  /**
   * Splits an equality inference according to the given subproofs.
   *
   * @param equality The equality inference to be split.
   * @param subProofs A list of 3-tuples whose first components are the subproofs for which the equality inference is
   *                  split; the second component are sequent connectors relating the equality's upper sequent with the
   *                  conclusion of the respective subproofs; the third component are the replacement contexts which
   *                  are used if the equality inference is split for the corresponding subproof.
   * @return A pair whose first component is list of proofs which are obtained from the given subproofs by inserting an
   *         equality inference as last inference if the conclusion of the subproof contains a parent of the auxiliary
   *         formula of the given equality inference. If an equality is inserted to a subproof but the equality formula
   *         has no parent in the subproof's conclusion, then a weakening inference introducing the equality formula is
   *         added right above the equality inference. Each resulting proof has a sequent connector which relates the
   *         given proof's conclusion with the conclusion of the new proof. The second component of the returned tuple
   *         is a boolean indicating whether a weakening inference was added to some resulting proof.
   */
  def apply( equality: EqualityRule, subProofs: Seq[( LKProof, SequentConnector, Abs )] ): ( Seq[( LKProof, SequentConnector )], Boolean ) = {
    val results: Seq[( LKProof, SequentConnector, Boolean )] =
      for {
        ( subProof, connector, replacementContext ) <- subProofs
      } yield {
        if ( connector.parents( equality.aux ).nonEmpty ) insertEquality( equality, subProof, connector, replacementContext )
        else ( subProof, SequentConnector( subProof.conclusion ), false )
      }
    (
      results map { case ( proof, connector, _ ) => ( proof, connector ) },
      results exists { _._3 } )
  }

  /**
   * Inserts an equality inference as last inference of the given subproof.
   *
   * @param equality Describes the formulas on which inserted equality inference operates.
   * @param subProof The subproof to which the equality inference is added.
   * @param connector Defines the parents of formulas in the equality's upper sequent in the subproof's conclusion.
   * @param replacementContext The replacement context which is used for the new equality inference.
   * @return A 3-tuple consisting of: A proof obtained by adding an equality inference to the specified subproof for
   *         the parents of the formulas described by the given equality inference and the sequent connector. A
   *         weakening weakening inference is added immediately above the new equality inference if the equality
   *         formula has no parent in the given subproof; A sequent connector which describes the parent formulas with
   *         respect to the given subproof's conclusion and the newly introduced inferences; A boolean indicating
   *         whether a weakening inference was added.
   */
  private def insertEquality( equality: EqualityRule, subProof: LKProof, connector: SequentConnector, replacementContext: Abs ): ( LKProof, SequentConnector, Boolean ) = {
    if ( connector.parents( equality.eq ) == Seq() ) {
      val newSubProof = WeakeningLeftRule( subProof, equality.equation )
      val ( newProof, newProofConnector ) = createEquality(
        newSubProof,
        newSubProof.mainIndices.head,
        newSubProof.getSequentConnector.child( connector.parent( equality.aux ) ),
        replacementContext )
      ( newProof, newProofConnector * newSubProof.getSequentConnector, true )
    } else {
      val ( newProof, newProofConnector ) = createEquality(
        subProof,
        connector.parent( equality.eq ),
        connector.parent( equality.aux ),
        replacementContext )
      ( newProof, newProofConnector, false )
    }
  }

  /**
   * Inserts an equality inference as the last inference of the given proof.
   *
   * @param subProof The proof to which the equality inference is added.
   * @param equation The index of the equality formula in the proof's conclusion.
   * @param auxiliary The index of the auxiliary formula in the proof's conclusion.
   * @param replacementContext The replacement context which is to be used for the equality inference.
   * @return A proof obtained from the given proof by adding an equality inference with the given parameters
   *         as the last inference.
   */
  private def createEquality(
    subProof: LKProof, equation: SequentIndex, auxiliary: SequentIndex, replacementContext: Abs ): ( LKProof, SequentConnector ) =
    auxiliary match {
      case Suc( _ ) =>
        val equalityInference = EqualityRightRule( subProof, equation, auxiliary, replacementContext )
        ( equalityInference, equalityInference.getSequentConnector )
      case Ant( _ ) =>
        val equalityInference = EqualityLeftRule( subProof, equation, auxiliary, replacementContext )
        ( equalityInference, equalityInference.getSequentConnector )
    }
}
