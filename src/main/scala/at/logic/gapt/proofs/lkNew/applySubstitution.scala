package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import BetaReduction._
import at.logic.gapt.proofs.SequentIndex

object applySubstitution {
  def apply( substitution: Substitution )( proof: LKProof ): LKProof = proof match {
    case InitialSequent( sequent ) =>
      Axiom( sequent.map { f => betaNormalize( substitution( f ) ) } )

    case WeakeningLeftRule( subProof, f ) =>
      val subProofNew = apply( substitution )( subProof )
      WeakeningLeftRule( subProofNew, betaNormalize( substitution( f ) ) )

    case WeakeningRightRule( subProof, f ) =>
      val subProofNew = apply( substitution )( subProof )
      WeakeningRightRule( subProofNew, betaNormalize( substitution( f ) ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution )( subProof )
      ContractionLeftRule( subProofNew, aux1, aux2 )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution )( subProof )
      ContractionRightRule( subProofNew, aux1, aux2 )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution )( leftSubProof ), apply( substitution )( rightSubProof ) )
      CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case NegLeftRule( subProof, aux ) =>
      val subProofNew = apply( substitution )( subProof )
      NegLeftRule( subProofNew, aux )

    case NegRightRule( subProof, aux ) =>
      val subProofNew = apply( substitution )( subProof )
      NegRightRule( subProofNew, aux )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution )( subProof )
      AndLeftRule( subProofNew, aux1, aux2 )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution )( leftSubProof ), apply( substitution )( rightSubProof ) )
      AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution )( leftSubProof ), apply( substitution )( rightSubProof ) )
      OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution )( subProof )
      OrRightRule( subProofNew, aux1, aux2 )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution )( leftSubProof ), apply( substitution )( rightSubProof ) )
      ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution )( subProof )
      ImpRightRule( subProofNew, aux1, aux2 )

    case ForallLeftRule( subProof, aux, f, term, v ) =>
      val subProofNew = apply( substitution )( subProof )
      ForallLeftRule( subProofNew, aux, betaNormalize( substitution( f ) ), betaNormalize( substitution( term ) ), v )

    case ForallRightRule( subProof, aux, eigen, quant ) =>
      require( !substitution.map.contains( eigen ), s"Cannot apply substitution: Eigenvariable $eigen is contained in domain." )
      val subProofNew = apply( substitution )( subProof )
      ForallRightRule( subProofNew, aux, eigen, quant )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      require( !substitution.map.contains( eigen ), s"Cannot apply substitution: Eigenvariable $eigen is contained in domain." )
      val subProofNew = apply( substitution )( subProof )
      ExistsLeftRule( subProofNew, aux, eigen, quant )

    case ExistsRightRule( subProof, aux, f, term, v ) =>
      val subProofNew = apply( substitution )( subProof )
      ExistsRightRule( subProofNew, aux, betaNormalize( substitution( f ) ), betaNormalize( substitution( term ) ), v )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val subProofNew = apply( substitution )( subProof )
      EqualityLeftRule( subProofNew, eq, aux, pos )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val subProofNew = apply( substitution )( subProof )
      EqualityRightRule( subProofNew, eq, aux, pos )

    case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution )( leftSubProof ), apply( substitution )( rightSubProof ) )
      InductionRule( leftSubProofNew, aux1, rightSubProofNew, aux2, aux3, betaNormalize( substitution( term ) ).asInstanceOf[FOLTerm] )

    case DefinitionLeftRule( subProof, aux, main ) =>
      val subProofNew = apply( substitution )( subProof )
      DefinitionLeftRule( subProofNew, aux, betaNormalize( substitution( main ) ) )

    case DefinitionRightRule( subProof, aux, main ) =>
      val subProofNew = apply( substitution )( subProof )
      DefinitionRightRule( subProofNew, aux, betaNormalize( substitution( main ) ) )

    case _ => throw new IllegalArgumentException( s"This rule is not handled at this time." )
  }
}
