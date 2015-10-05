package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr.{ Substitution, rename, variables, Var }
import at.logic.gapt.proofs.{ Sequent, SequentIndex }

object Utils {
  /**
   * @return true iff this proof contains a reflexivity axiom or an equational inference
   */
  def containsEqualityReasoning( p: LKProof ): Boolean = p match {
    case ReflexivityAxiom( _ )                           => true
    case EqualityLeftRule( _, _, _, _ )                  => true
    case EqualityRightRule( _, _, _, _ )                 => true
    case InitialSequent( seq )                           => false
    case UnaryLKProof( _, subProof )                     => containsEqualityReasoning( subProof )
    case BinaryLKProof( _, leftSubProof, rightSubProof ) => containsEqualityReasoning( leftSubProof ) || containsEqualityReasoning( rightSubProof )
  }
}

object regularize {
  def apply( proof: LKProof ) = apply_( proof, variables( proof ) )._1

  def apply_( proof: LKProof, blacklist: Set[Var] ): ( LKProof, Set[Var] ) = proof match {
    case InitialSequent( sequent ) =>
      ( proof, blacklist )

    case WeakeningLeftRule( subProof, f ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( WeakeningLeftRule( subProofNew, f ), blacklistNew )

    case WeakeningRightRule( subProof, f ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( WeakeningRightRule( subProofNew, f ), blacklistNew )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( ContractionLeftRule( subProofNew, aux1, aux2 ), blacklistNew )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( ContractionRightRule( subProofNew, aux1, aux2 ), blacklistNew )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, blacklistNew_ ) = apply_( leftSubProof, blacklist )
      val ( rightSubProofNew, blacklistNew ) = apply_( rightSubProof, blacklistNew_ )

      ( CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 ), blacklistNew )

    case NegLeftRule( subProof, aux ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( NegLeftRule( subProofNew, aux ), blacklistNew )

    case NegRightRule( subProof, aux ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( NegRightRule( subProofNew, aux ), blacklistNew )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( AndLeftRule( subProofNew, aux1, aux2 ), blacklistNew )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, blacklistNew_ ) = apply_( leftSubProof, blacklist )
      val ( rightSubProofNew, blacklistNew ) = apply_( rightSubProof, blacklistNew_ )

      ( AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 ), blacklistNew )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, blacklistNew_ ) = apply_( leftSubProof, blacklist )
      val ( rightSubProofNew, blacklistNew ) = apply_( rightSubProof, blacklistNew_ )

      ( OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 ), blacklistNew )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )

      ( OrRightRule( subProofNew, aux1, aux2 ), blacklistNew )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, blacklistNew_ ) = apply_( leftSubProof, blacklist )
      val ( rightSubProofNew, blacklistNew ) = apply_( rightSubProof, blacklistNew_ )

      ( ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 ), blacklistNew )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )

      ( ImpRightRule( subProofNew, aux1, aux2 ), blacklistNew )

    case ForallLeftRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( ForallLeftRule( subProofNew, aux, f, term, v ), blacklistNew )

    case ForallRightRule( subProof, aux, eigen, quant ) =>

      val ( subProofNew_, blacklistNew ) = apply_( subProof, blacklist + eigen )

      if ( blacklistNew contains eigen ) {
        val eigenNew = rename( eigen, blacklistNew.toList )
        val subProofNew = applySubstitution( Substitution( eigen, eigenNew ) )( subProofNew_ )
        ( ForallRightRule( subProofNew, aux, eigenNew, quant ), blacklistNew + eigenNew )
      } else ( ForallRightRule( subProofNew_, aux, eigen, quant ), blacklistNew + eigen )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>

      val ( subProofNew_, blacklistNew ) = apply_( subProof, blacklist + eigen )

      if ( blacklistNew contains eigen ) {
        val eigenNew = rename( eigen, blacklistNew.toList )
        val subProofNew = applySubstitution( Substitution( eigen, eigenNew ) )( subProofNew_ )
        ( ExistsLeftRule( subProofNew, aux, eigenNew, quant ), blacklistNew + eigenNew )
      } else ( ExistsLeftRule( subProofNew_, aux, eigen, quant ), blacklistNew + eigen )

    case ExistsRightRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( ExistsRightRule( subProofNew, aux, f, term, v ), blacklistNew )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( EqualityLeftRule( subProofNew, eq, aux, pos ), blacklistNew )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( EqualityRightRule( subProofNew, eq, aux, pos ), blacklistNew )

    //FIXME: This should probably be treated properly
    case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
      val ( leftSubProofNew, blacklistNew_ ) = apply_( leftSubProof, blacklist )
      val ( rightSubProofNew, blacklistNew ) = apply_( rightSubProof, blacklistNew_ )
      ( InductionRule( leftSubProofNew, aux1, rightSubProofNew, aux2, aux3, term ), blacklistNew )

    case DefinitionLeftRule( subProof, aux, main ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( DefinitionLeftRule( subProofNew, aux, main ), blacklistNew )

    case DefinitionRightRule( subProof, aux, main ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( DefinitionRightRule( subProofNew, aux, main ), blacklistNew )

    case _ => throw new IllegalArgumentException( s"This rule is not handled at this time." )
  }
}
