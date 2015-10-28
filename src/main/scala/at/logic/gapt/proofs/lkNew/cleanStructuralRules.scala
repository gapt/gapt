package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, SequentIndex, Ant, OccConnector }

object cleanStructuralRules {
  def apply( proof: LKProof ) = {
    val ( subProof, connector ) = apply2( proof )
    WeakeningMacroRule( subProof, connector.upperSequent )
  }

  private def apply_( proof: LKProof ): ( LKProof, Seq[HOLFormula], Seq[HOLFormula] ) = proof match {
    case InitialSequent( _ ) =>
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

    case InductionRule( cases, main ) =>
      val proofNew = InductionRule( cases map {
        case InductionCase( subProof, constructor, hypotheses, eigenVars, conclusion ) =>
          val subProofNew = WeakeningMacroRule( apply_( subProof )._1, subProof.endSequent.zipWithIndex.filter { case ( _, i ) => i == conclusion || hypotheses.contains( i ) }.map { _._1 }, strict = false )
          InductionCase( subProofNew, constructor,
            hypotheses map { h => subProofNew.endSequent indexOfInAnt subProof.endSequent( h ) },
            eigenVars,
            subProofNew.endSequent indexOfInSuc subProof.endSequent( conclusion ) )
      }, main )
      ( proofNew, proof.endSequent.antecedent diff proofNew.endSequent.antecedent,
        proof.endSequent.succedent diff proofNew.endSequent.succedent )

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
          ExistsLeftRule( subProofNew, Ex( quant, auxFormula ), eigen ),
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
  }

  def apply2( proof: LKProof, reductive: Boolean = true ): ( LKProof, OccConnector[HOLFormula] ) = proof match {
    case InitialSequent( sequent ) =>
      ( proof, OccConnector( sequent ) )

    case p @ WeakeningLeftRule( subProof, formula ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )
      ( subProofNew, subConnector * p.getOccConnector.inv )

    case p @ WeakeningRightRule( subProof, formula ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )
      ( subProofNew, subConnector * p.getOccConnector.inv )

    case p @ ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) =>
          val proofNew = ContractionLeftRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) =>
          val proofNew = ContractionRightRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply2( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply2( rightSubProof, reductive )

      if ( reductive )
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {
          case ( Seq( a1 ), Seq( a2 ) ) =>
            val proofNew = CutRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftOccConnector * leftSubConnector * p.getLeftOccConnector.inv )
              + ( proofNew.getRightOccConnector * rightSubConnector * p.getRightOccConnector.inv ) )

          case ( Seq( a1 ), Seq() ) =>
            ( rightSubProofNew, rightSubConnector * p.getRightOccConnector.inv )

          case ( Seq(), Seq( a2 ) ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )

          case ( Seq(), Seq() ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )
        }

      else {
        val ( leftSubProofNew_, leftSubConnector_ ) = introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) = introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = CutRule( leftSubProofNew_, leftSubConnector_.child( aux1 ), rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector_ * p.getLeftOccConnector.inv )
          + ( proofNew.getRightOccConnector * rightSubConnector_ * p.getRightOccConnector.inv ) )
      }

    case p @ InductionRule( cases, main ) =>

      val ( subProofsNew, subConnectors ) = cases.map { c => apply2( c.proof, reductive ) }.unzip

      def isWeak( i: Int ): Boolean = {
        val weakHypos = for ( h <- cases( i ).hypotheses ) yield subConnectors( i ).children( h ).isEmpty
        weakHypos.forall( _ == true ) && subConnectors( i ).children( cases( i ).conclusion ).isEmpty
      }

      val weakIndex = cases.indices.find( isWeak )

      if ( reductive && weakIndex.nonEmpty ) {
        val i = weakIndex.get
        val ( subProofNew, subConnector ) = ( subProofsNew( i ), subConnectors( i ) )

        ( subProofNew, subConnector * p.occConnectors( i ).inv )
      } else {
        val ( casesNew, subConnectorsNew ) = ( for ( c <- cases ) yield {
          val ( subProofNew, subConnector ) = apply2( c.proof )
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( c.proof, subProofNew, subConnector, c.hypotheses :+ c.conclusion )
          val hypothesesNew = c.hypotheses map { h => subConnector_.child( h ) }
          val conclusionNew = subConnector_.child( c.conclusion )

          ( InductionCase( subProofNew_, c.constructor, hypothesesNew, c.eigenVars, conclusionNew ), subConnector_ )
        } ).unzip

        val proofNew = InductionRule( casesNew, main )
        val occConnectorsNew = for ( i <- p.immediateSubProofs.indices ) yield proofNew.occConnectors( i ) * subConnectorsNew( i ) * p.occConnectors( i ).inv

        val occConnectorNew = occConnectorsNew.reduceLeft( _ + _ )
        ( proofNew, occConnectorNew )
      }

    case p @ NegLeftRule( subProof, aux ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = NegLeftRule( subProofNew, a )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ NegRightRule( subProof, aux ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = NegRightRule( subProofNew, a )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) =>
          val proofNew = AndLeftRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case ( Seq(), Seq() ) =>
          ( subProofNew, subConnector * p.getOccConnector.inv )

        case _ =>
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( subProof, subProofNew, subConnector, Seq( aux1, aux2 ) )
          val proofNew = AndLeftRule( subProofNew_, subConnector_.child( aux1 ), subConnector_.child( aux2 ) )
          ( proofNew, proofNew.getOccConnector * subConnector_ * p.getOccConnector.inv )
      }

    case p @ AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply2( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply2( rightSubProof, reductive )

      if ( reductive )
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {
          case ( Seq( a1 ), Seq( a2 ) ) =>
            val proofNew = AndRightRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftOccConnector * leftSubConnector * p.getLeftOccConnector.inv )
              + ( proofNew.getRightOccConnector * rightSubConnector * p.getRightOccConnector.inv ) )

          case ( Seq( a1 ), Seq() ) =>
            ( rightSubProofNew, rightSubConnector * p.getRightOccConnector.inv )

          case ( Seq(), Seq( a2 ) ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )

          case ( Seq(), Seq() ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )
        }

      else {
        val ( leftSubProofNew_, leftSubConnector_ ) = introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) = introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = AndRightRule( leftSubProofNew_, leftSubConnector_.child( aux1 ), rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector_ * p.getLeftOccConnector.inv )
          + ( proofNew.getRightOccConnector * rightSubConnector_ * p.getRightOccConnector.inv ) )
      }

    case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply2( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply2( rightSubProof, reductive )

      if ( reductive )
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {
          case ( Seq( a1 ), Seq( a2 ) ) =>
            val proofNew = OrLeftRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftOccConnector * leftSubConnector * p.getLeftOccConnector.inv )
              + ( proofNew.getRightOccConnector * rightSubConnector * p.getRightOccConnector.inv ) )

          case ( Seq( a1 ), Seq() ) =>
            ( rightSubProofNew, rightSubConnector * p.getRightOccConnector.inv )

          case ( Seq(), Seq( a2 ) ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )

          case ( Seq(), Seq() ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )
        }

      else {
        val ( leftSubProofNew_, leftSubConnector_ ) = introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) = introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = OrLeftRule( leftSubProofNew_, leftSubConnector_.child( aux1 ), rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector_ * p.getLeftOccConnector.inv )
          + ( proofNew.getRightOccConnector * rightSubConnector_ * p.getRightOccConnector.inv ) )
      }

    case p @ OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) =>
          val proofNew = OrRightRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case ( Seq(), Seq() ) =>
          ( subProofNew, subConnector * p.getOccConnector.inv )

        case _ =>
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( subProof, subProofNew, subConnector, Seq( aux1, aux2 ) )
          val proofNew = OrRightRule( subProofNew_, subConnector_.child( aux1 ), subConnector_.child( aux2 ) )
          ( proofNew, proofNew.getOccConnector * subConnector_ * p.getOccConnector.inv )
      }

    case p @ ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply2( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply2( rightSubProof, reductive )

      if ( reductive )
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {
          case ( Seq( a1 ), Seq( a2 ) ) =>
            val proofNew = ImpLeftRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftOccConnector * leftSubConnector * p.getLeftOccConnector.inv )
              + ( proofNew.getRightOccConnector * rightSubConnector * p.getRightOccConnector.inv ) )

          case ( Seq( a1 ), Seq() ) =>
            ( rightSubProofNew, rightSubConnector * p.getRightOccConnector.inv )

          case ( Seq(), Seq( a2 ) ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )

          case ( Seq(), Seq() ) =>
            ( leftSubProofNew, leftSubConnector * p.getLeftOccConnector.inv )
        }

      else {
        val ( leftSubProofNew_, leftSubConnector_ ) = introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) = introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = ImpLeftRule( leftSubProofNew_, leftSubConnector_.child( aux1 ), rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector_ * p.getLeftOccConnector.inv )
          + ( proofNew.getRightOccConnector * rightSubConnector_ * p.getRightOccConnector.inv ) )
      }

    case p @ ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) =>
          val proofNew = ImpRightRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case ( Seq(), Seq() ) =>
          ( subProofNew, subConnector * p.getOccConnector.inv )

        case _ =>
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( subProof, subProofNew, subConnector, Seq( aux1, aux2 ) )
          val proofNew = ImpRightRule( subProofNew_, subConnector_.child( aux1 ), subConnector_.child( aux2 ) )
          ( proofNew, proofNew.getOccConnector * subConnector_ * p.getOccConnector.inv )
      }

    case p @ ForallLeftRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = ForallLeftRule( subProofNew, a, f, term, v )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ ForallRightRule( subProof, aux, eigen, quant ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = ForallRightRule( subProofNew, a, eigen, quant )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = ExistsLeftRule( subProofNew, a, eigen, quant )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ ExistsRightRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = ExistsRightRule( subProofNew, a, f, term, v )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( eq ), subConnector.children( aux ) ) match {
        case ( _, Seq() ) =>
          ( subProofNew, subConnector * p.getOccConnector.inv )

        case _ =>
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( subProof, subProofNew, subConnector, Seq( eq ) )
          val proofNew = EqualityLeftRule( subProofNew_, subConnector_.child( eq ), subConnector_.child( aux ), pos )
          ( proofNew, proofNew.getOccConnector * subConnector_ * p.getOccConnector.inv )
      }

    case p @ EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      ( subConnector.children( eq ), subConnector.children( aux ) ) match {
        case ( _, Seq() ) =>
          ( subProofNew, subConnector * p.getOccConnector.inv )

        case _ =>
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( subProof, subProofNew, subConnector, Seq( eq ) )
          val proofNew = EqualityRightRule( subProofNew_, subConnector_.child( eq ), subConnector_.child( aux ), pos )
          ( proofNew, proofNew.getOccConnector * subConnector_ * p.getOccConnector.inv )
      }

    case p @ DefinitionLeftRule( subProof, aux, main ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = DefinitionLeftRule( subProofNew, a, main )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }

    case p @ DefinitionRightRule( subProof, aux, main ) =>
      val ( subProofNew, subConnector ) = apply2( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) =>
          val proofNew = DefinitionRightRule( subProofNew, a, main )
          ( proofNew, proofNew.getOccConnector * subConnector * p.getOccConnector.inv )

        case _ =>
          ( subProofNew, subConnector * p.getOccConnector.inv )
      }
  }

  private def introduceWeakenings( subProofOld: LKProof, subProofNew: LKProof, subConnector: OccConnector[HOLFormula], weakFormulas: Seq[SequentIndex] ): ( LKProof, OccConnector[HOLFormula] ) = {
    val premise = subProofOld.endSequent

    ( ( subProofNew, subConnector ) /: weakFormulas ) { ( acc, idx ) =>
      val ( currentProof, currentOC ) = acc

      if ( currentOC.children( idx ).nonEmpty )
        ( currentProof, currentOC )

      else idx match {

        case Ant( _ ) =>
          val newProof = WeakeningLeftRule( currentProof, premise( idx ) )
          val oc = newProof.getOccConnector
          ( newProof, ( oc * currentOC ) + ( Ant( 0 ), idx ) )

        case Suc( _ ) =>
          val newProof = WeakeningRightRule( currentProof, premise( idx ) )
          val oc = newProof.getOccConnector
          val mainIdx = newProof.mainIndices.head
          ( newProof, ( oc * currentOC ) + ( mainIdx, idx ) )
      }

    }
  }

}