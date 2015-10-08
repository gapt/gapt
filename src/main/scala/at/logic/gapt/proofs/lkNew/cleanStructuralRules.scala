package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._

object cleanStructuralRules {
  def apply( proof: LKProof ) = {
    val ( subProof, weakAnt, weakSuc ) = apply_( proof )
    WeakeningMacroRule( subProof, weakAnt, weakSuc )
  }

  private def apply_( proof: LKProof ): ( LKProof, Seq[HOLFormula], Seq[HOLFormula] ) = proof match {
    case LogicalAxiom( _ ) | ReflexivityAxiom( _ ) | BottomAxiom | TopAxiom =>
      ( proof, Seq(), Seq() )

    case WeakeningLeftRule( subProof, formula ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      ( subProofNew, formula +: weakAnt, weakSuc )

    case WeakeningRightRule( subProof, formula ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      ( subProofNew, weakAnt, formula +: weakSuc )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val mainFormula = proof.mainFormulas.head

      weakAnt.count( _ == mainFormula ) match {
        case 0 => ( ContractionLeftRule( subProofNew, mainFormula ), weakAnt, weakSuc )
        case _ => ( subProofNew, weakAnt diff Seq( mainFormula ), weakSuc )
      }

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val mainFormula = proof.mainFormulas.head

      weakSuc.count( _ == mainFormula ) match {
        case 0 => ( ContractionRightRule( subProofNew, mainFormula ), weakAnt, weakSuc )
        case _ => ( subProofNew, weakAnt, weakSuc diff Seq( mainFormula ) )
      }

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val cutFormula = leftSubProof.endSequent( aux1 )
      val ( leftSubproofNew, leftWeakAnt, leftWeakSuc ) = apply_( leftSubProof )
      val ( rightSubproofNew, rightWeakAnt, rightWeakSuc ) = apply_( rightSubProof )

      ( leftWeakSuc contains cutFormula, rightWeakAnt contains cutFormula ) match {
        case ( true, true ) =>
          ( leftSubproofNew,
            leftWeakAnt ++ rightWeakAnt.diff( Seq( cutFormula ) ) ++ rightSubproofNew.endSequent.antecedent,
            leftWeakSuc.diff( Seq( cutFormula ) ) ++ rightWeakSuc ++ rightSubproofNew.endSequent.succedent )

        case ( true, false ) =>
          ( leftSubproofNew,
            leftWeakAnt ++ rightWeakAnt ++ rightSubproofNew.endSequent.antecedent.diff( Seq( cutFormula ) ),
            leftWeakSuc.diff( Seq( cutFormula ) ) ++ rightWeakSuc ++ rightSubproofNew.endSequent.succedent )

        case ( false, true ) =>
          ( rightSubproofNew,
            leftWeakAnt ++ rightWeakAnt.diff( Seq( cutFormula ) ) ++ leftSubproofNew.endSequent.antecedent,
            leftWeakSuc ++ rightWeakSuc ++ leftSubproofNew.endSequent.succedent.diff( Seq( cutFormula ) ) )

        case ( false, false ) =>
          ( CutRule( leftSubproofNew, rightSubproofNew, cutFormula ),
            leftWeakAnt ++ rightWeakAnt,
            leftWeakSuc ++ rightWeakSuc )
      }

    case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
      val ( inductionBase, inductionHypo, inductionStep ) = ( proof.auxFormulas( 0 )( 0 ), proof.auxFormulas( 1 )( 0 ), proof.auxFormulas( 1 )( 1 ) )
      val ( leftSubproofNew, leftWeakAnt, leftWeakSuc ) = apply_( leftSubProof )
      val ( rightSubproofNew, rightWeakAnt, rightWeakSuc ) = apply_( rightSubProof )

      ( leftWeakSuc contains inductionBase, rightWeakAnt contains inductionHypo, rightWeakSuc contains inductionStep ) match {
        case ( true, _, _ ) => //In this case, we delete the right subproof (i.e. the induction step).
          ( leftSubproofNew,
            leftWeakAnt ++ rightWeakAnt ++ rightSubproofNew.endSequent.antecedent.diff( Seq( inductionHypo ) ),
            leftWeakSuc.diff( Seq( inductionBase ) ) ++ rightWeakSuc ++ rightSubproofNew.endSequent.succedent.diff( Seq( inductionStep ) ) )

        case ( false, true, true ) => //In this case, we delete the left subproof (i.e. the induction base).
          ( rightSubproofNew,
            leftWeakAnt ++ rightWeakAnt.diff( Seq( inductionHypo ) ) ++ leftSubproofNew.endSequent.antecedent,
            leftWeakSuc ++ rightWeakSuc.diff( Seq( inductionStep ) ) ++ leftSubproofNew.endSequent.succedent.diff( Seq( inductionBase ) ) )

        case ( false, true, false ) =>
          ( InductionRule( leftSubproofNew, inductionBase.asInstanceOf[FOLFormula], WeakeningLeftRule( rightSubproofNew, inductionHypo ), inductionHypo.asInstanceOf[FOLFormula], inductionStep.asInstanceOf[FOLFormula], term ),
            leftWeakAnt ++ rightWeakAnt.diff( Seq( inductionHypo ) ),
            leftWeakSuc ++ rightWeakSuc )

        case ( false, false, true ) =>
          ( InductionRule( leftSubproofNew, inductionBase.asInstanceOf[FOLFormula], WeakeningRightRule( rightSubproofNew, inductionStep ), inductionHypo.asInstanceOf[FOLFormula], inductionStep.asInstanceOf[FOLFormula], term ),
            leftWeakAnt ++ rightWeakAnt,
            leftWeakSuc ++ rightWeakSuc.diff( Seq( inductionStep ) ) )

        case ( false, false, false ) =>
          ( InductionRule( leftSubproofNew, inductionBase.asInstanceOf[FOLFormula], rightSubproofNew, inductionHypo.asInstanceOf[FOLFormula], inductionStep.asInstanceOf[FOLFormula], term ),
            leftWeakAnt ++ rightWeakAnt,
            leftWeakSuc ++ rightWeakSuc )

      }

    case NegLeftRule( subProof, aux ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakSuc contains auxFormula )
        (
          subProofNew,
          Neg( auxFormula ) +: weakAnt,
          weakSuc.diff( Seq( auxFormula ) )
        )
      else
        (
          NegLeftRule( subProofNew, auxFormula ),
          weakAnt,
          weakSuc
        )

    case NegRightRule( subProof, aux ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakAnt contains auxFormula )
        ( subProofNew,
          Neg( auxFormula ) +: weakAnt.diff( Seq( auxFormula ) ),
          Neg( auxFormula ) +: weakSuc )
      else
        (
          NegRightRule( subProofNew, auxFormula ),
          weakAnt,
          weakSuc
        )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val leftConjunct = proof.auxFormulas.head( 0 )
      val rightConjunct = proof.auxFormulas.head( 1 )

      ( weakAnt contains leftConjunct, weakAnt contains rightConjunct ) match {
        case ( true, true ) =>
          (
            subProofNew,
            And( leftConjunct, rightConjunct ) +: weakAnt.diff( Seq( leftConjunct, rightConjunct ) ),
            weakSuc
          )

        case ( false, true ) =>
          (
            AndLeftRule( WeakeningLeftRule( subProofNew, rightConjunct ), leftConjunct, rightConjunct ),
            weakAnt.diff( Seq( rightConjunct ) ),
            weakSuc
          )

        case ( true, false ) =>
          (
            AndLeftRule( WeakeningLeftRule( subProofNew, leftConjunct ), leftConjunct, rightConjunct ),
            weakAnt.diff( Seq( leftConjunct ) ),
            weakSuc
          )

        case ( false, false ) =>
          (
            AndLeftRule( subProofNew, leftConjunct, rightConjunct ),
            weakAnt,
            weakSuc
          )
      }

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val leftConjunct = proof.auxFormulas.head( 0 )
      val rightConjunct = proof.auxFormulas.tail.head( 0 )

      val ( leftSubproofNew, leftWeakAnt, leftWeakSuc ) = apply_( leftSubProof )
      val ( rightSubproofNew, rightWeakAnt, rightWeakSuc ) = apply_( rightSubProof )

      ( leftWeakSuc contains leftConjunct, rightWeakSuc contains rightConjunct ) match {
        case ( true, _ ) =>
          ( leftSubproofNew,
            leftWeakAnt ++ rightWeakAnt ++ rightSubproofNew.endSequent.antecedent,
            And( leftConjunct, rightConjunct ) +: ( leftWeakSuc.diff( Seq( leftConjunct ) ) ++ rightWeakSuc ++ rightSubproofNew.endSequent.succedent.diff( Seq( rightConjunct ) ) ) )

        case ( false, true ) =>
          ( rightSubproofNew,
            leftWeakAnt ++ rightWeakAnt ++ leftSubproofNew.endSequent.antecedent,
            And( leftConjunct, rightConjunct ) +: ( leftWeakSuc ++ rightWeakSuc.diff( Seq( rightConjunct ) ) ++ leftSubproofNew.endSequent.succedent.diff( Seq( leftConjunct ) ) ) )

        case ( false, false ) =>
          ( AndRightRule( leftSubproofNew, leftConjunct, rightSubproofNew, rightConjunct ),
            leftWeakAnt ++ rightWeakAnt,
            leftWeakSuc ++ rightWeakSuc )
      }

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val leftDisjunct = proof.auxFormulas.head( 0 )
      val rightDisjunct = proof.auxFormulas.tail.head( 0 )

      val ( leftSubproofNew, leftWeakAnt, leftWeakSuc ) = apply_( leftSubProof )
      val ( rightSubproofNew, rightWeakAnt, rightWeakSuc ) = apply_( rightSubProof )

      ( leftWeakAnt contains leftDisjunct, rightWeakAnt contains rightDisjunct ) match {
        case ( true, _ ) =>
          ( leftSubproofNew,
            Or( leftDisjunct, rightDisjunct ) +: ( leftWeakAnt.diff( Seq( leftDisjunct ) ) ++ rightWeakAnt ++ rightSubproofNew.endSequent.antecedent.diff( Seq( rightDisjunct ) ) ),
            leftWeakSuc ++ rightWeakSuc ++ rightSubproofNew.endSequent.succedent )

        case ( false, true ) =>
          ( rightSubproofNew,
            Or( leftDisjunct, rightDisjunct ) +: ( leftWeakAnt ++ rightWeakAnt.diff( Seq( rightDisjunct ) ) ++ leftSubproofNew.endSequent.antecedent.diff( Seq( leftDisjunct ) ) ),
            leftWeakSuc ++ rightWeakSuc ++ leftSubproofNew.endSequent.succedent )

        case ( false, false ) =>
          ( OrLeftRule( leftSubproofNew, leftDisjunct, rightSubproofNew, rightDisjunct ),
            leftWeakAnt ++ rightWeakAnt,
            leftWeakSuc ++ rightWeakSuc )
      }

    case OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val leftDisjunct = proof.auxFormulas.head( 0 )
      val rightDisjunct = proof.auxFormulas.head( 1 )

      ( weakSuc contains leftDisjunct, weakSuc contains rightDisjunct ) match {
        case ( true, true ) =>
          (
            subProofNew,
            weakAnt,
            Or( leftDisjunct, rightDisjunct ) +: weakSuc.diff( Seq( leftDisjunct, rightDisjunct ) )
          )

        case ( false, true ) =>
          (
            OrRightRule( WeakeningRightRule( subProofNew, rightDisjunct ), leftDisjunct, rightDisjunct ),
            weakAnt,
            weakSuc.diff( Seq( rightDisjunct ) )
          )

        case ( true, false ) =>
          (
            OrRightRule( WeakeningRightRule( subProofNew, leftDisjunct ), leftDisjunct, rightDisjunct ),
            weakAnt,
            weakSuc.diff( Seq( leftDisjunct ) )
          )

        case ( false, false ) =>
          (
            OrRightRule( subProofNew, leftDisjunct, rightDisjunct ),
            weakAnt,
            weakSuc
          )
      }

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val impPremise = proof.auxFormulas.head( 0 )
      val impConclusion = proof.auxFormulas.tail.head( 0 )

      val ( leftSubproofNew, leftWeakAnt, leftWeakSuc ) = apply_( leftSubProof )
      val ( rightSubproofNew, rightWeakAnt, rightWeakSuc ) = apply_( rightSubProof )

      ( leftWeakSuc contains impPremise, rightWeakAnt contains impConclusion ) match {
        case ( true, _ ) =>
          ( leftSubproofNew,
            Imp( impPremise, impConclusion ) +: ( leftWeakAnt ++ rightWeakAnt ++ rightSubproofNew.endSequent.antecedent.diff( Seq( impConclusion ) ) ),
            leftWeakSuc.diff( Seq( impPremise ) ) ++ rightWeakSuc ++ rightSubproofNew.endSequent.succedent )

        case ( false, true ) =>
          ( rightSubproofNew,
            Imp( impPremise, impConclusion ) +: ( leftWeakAnt ++ rightWeakAnt.diff( Seq( impConclusion ) ) ++ leftSubproofNew.endSequent.antecedent ),
            leftWeakSuc ++ rightWeakSuc ++ leftSubproofNew.endSequent.succedent.diff( Seq( impPremise ) ) )

        case ( false, false ) =>
          ( ImpLeftRule( leftSubproofNew, impPremise, rightSubproofNew, impConclusion ),
            leftWeakAnt ++ rightWeakAnt,
            leftWeakSuc ++ rightWeakSuc )
      }

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val impPremise = proof.auxFormulas.head( 0 )
      val impConclusion = proof.auxFormulas.head( 1 )

      ( weakAnt contains impPremise, weakSuc contains impConclusion ) match {
        case ( true, true ) =>
          (
            subProofNew,
            weakAnt.diff( Seq( impPremise ) ),
            Imp( impPremise, impConclusion ) +: weakSuc.diff( Seq( impConclusion ) )
          )

        case ( false, true ) =>
          (
            ImpRightRule( WeakeningRightRule( subProofNew, impConclusion ), impPremise, impConclusion ),
            weakAnt,
            weakSuc.diff( Seq( impConclusion ) )
          )

        case ( true, false ) =>
          (
            ImpRightRule( WeakeningLeftRule( subProofNew, impPremise ), impPremise, impConclusion ),
            weakAnt.diff( Seq( impPremise ) ),
            weakSuc
          )

        case ( false, false ) =>
          (
            ImpRightRule( subProofNew, impPremise, impConclusion ),
            weakAnt,
            weakSuc
          )
      }

    case ForallLeftRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakAnt contains auxFormula )
        (
          subProofNew,
          All( v, f ) +: weakAnt.diff( Seq( auxFormula ) ),
          weakSuc
        )
      else
        (
          ForallLeftRule( subProofNew, All( v, f ), term ),
          weakAnt,
          weakSuc
        )

    case ForallRightRule( subProof, aux, eigen, quant ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakSuc contains auxFormula )
        (
          subProofNew,
          weakAnt,
          All( quant, auxFormula ) +: weakSuc.diff( Seq( auxFormula ) )
        )
      else
        (
          ForallRightRule( subProofNew, All( quant, auxFormula ), eigen ),
          weakAnt,
          weakSuc
        )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakAnt contains auxFormula )
        (
          subProofNew,
          Ex( quant, auxFormula ) +: weakAnt.diff( Seq( auxFormula ) ),
          weakSuc
        )
      else
        (
          ExistsRightRule( subProofNew, All( quant, auxFormula ), eigen ),
          weakAnt,
          weakSuc
        )

    case ExistsRightRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakSuc contains auxFormula )
        (
          subProofNew,
          weakAnt,
          Ex( v, f ) +: weakSuc.diff( Seq( auxFormula ) )
        )
      else
        (
          ExistsRightRule( subProofNew, Ex( v, f ), term ),
          weakAnt,
          weakSuc
        )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val equation = proof.auxFormulas.head( 0 )
      val auxFormula = proof.auxFormulas.head( 1 )
      val mainFormula = proof.mainFormulas.head

      ( weakAnt contains equation, weakAnt contains auxFormula ) match {
        case ( _, true ) =>
          val mainFormula = proof.mainFormulas.head
          (
            subProofNew,
            mainFormula +: weakAnt.diff( Seq( auxFormula ) ),
            weakSuc
          )

        case ( true, false ) =>
          (
            EqualityLeftRule( WeakeningLeftRule( subProofNew, equation ), equation, auxFormula, mainFormula ),
            weakAnt.diff( Seq( equation ) ),
            weakSuc
          )

        case ( false, false ) =>
          (
            EqualityLeftRule( subProofNew, equation, auxFormula, mainFormula ),
            weakAnt,
            weakSuc
          )
      }

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val equation = proof.auxFormulas.head( 0 )
      val auxFormula = proof.auxFormulas.head( 1 )
      val mainFormula = proof.mainFormulas.head

      ( weakAnt contains equation, weakSuc contains auxFormula ) match {
        case ( _, true ) =>
          val mainFormula = proof.mainFormulas.head
          (
            subProofNew,
            weakAnt,
            mainFormula +: weakSuc.diff( Seq( auxFormula ) )
          )

        case ( true, false ) =>
          (
            EqualityRightRule( WeakeningLeftRule( subProofNew, equation ), equation, auxFormula, mainFormula ),
            weakAnt.diff( Seq( equation ) ),
            weakSuc
          )

        case ( false, false ) =>
          (
            EqualityRightRule( subProofNew, equation, auxFormula, mainFormula ),
            weakAnt,
            weakSuc
          )
      }

    case DefinitionLeftRule( subProof, aux, main ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakAnt contains auxFormula )
        (
          subProofNew,
          main +: weakAnt.diff( Seq( auxFormula ) ),
          weakSuc
        )
      else
        (
          DefinitionLeftRule( subProofNew, auxFormula, main ),
          weakAnt,
          weakSuc
        )

    case DefinitionRightRule( subProof, aux, main ) =>
      val ( subProofNew, weakAnt, weakSuc ) = apply_( subProof )
      val auxFormula = proof.auxFormulas.head.head

      if ( weakSuc contains auxFormula )
        (
          subProofNew,
          weakAnt,
          main +: weakSuc.diff( Seq( auxFormula ) )
        )
      else
        (
          DefinitionRightRule( subProofNew, auxFormula, main ),
          weakAnt,
          weakSuc
        )

    case _ => throw new IllegalArgumentException( "This rule is not supported at this time." )
  }

}