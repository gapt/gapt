package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, SequentIndex }

object containsEqualityReasoning {
  /**
   * @param proof An LKProof.
   * @return true iff this proof contains a reflexivity axiom or an equational inference
   */
  def apply( proof: LKProof ): Boolean = proof match {
    case ReflexivityAxiom( _ )                           => true
    case EqualityLeftRule( _, _, _, _ )                  => true
    case EqualityRightRule( _, _, _, _ )                 => true
    case InitialSequent( seq )                           => false
    case UnaryLKProof( _, subProof )                     => containsEqualityReasoning( subProof )
    case BinaryLKProof( _, leftSubProof, rightSubProof ) => containsEqualityReasoning( leftSubProof ) || containsEqualityReasoning( rightSubProof )
  }
}

object freeVariablesLK {
  def apply( p: LKProof ): Set[Var] = p match {
    case StrongQuantifierRule( subProof, aux, eigen, quant, isSuc ) =>
      apply( subProof ) - eigen
    case _ =>
      freeVariables( p.conclusion ) ++ p.immediateSubProofs.flatMap( apply )
  }
}

object cutFormulas {
  def apply( proof: LKProof ) = proof.treeLike.postOrder.flatMap(
    {
      case CutRule( p, o, _, _ ) => List( p.conclusion( o ) )
      case _                     => List()
    }
  ).toSet
}

object isRegular {
  /**
   * Tests for regularity by checking whether all eigenvariables are distinct.
   *
   * @param proof An LKProof.
   * @return true iff proof is regular.
   */
  def apply( proof: LKProof ): Boolean = {
    val eigenVars = for ( Eigenvariable( v ) <- proof.treeLike.postOrder ) yield v
    eigenVars == eigenVars.distinct
  }
}

/**
 * Proof regularization
 *
 */
object regularize {
  /**
   * Renames all eigenvariables in a proof so that it becomes regular.
   *
   * @param proof An LKProof.
   * @return A regular LKProof.
   */
  def apply( proof: LKProof ) = apply_( proof, freeVariablesLK( proof ) )._1

  /**
   * Renames at least the eigenvariables contains in blacklist so that proof becomes regular.
   *
   * @param proof An LKProof.
   * @param blacklist A set of variables that must be renamed if they occur as eigenvariables.
   * @return A regular LKProof.
   */
  def apply( proof: LKProof, blacklist: Set[Var] ): LKProof = apply_( proof, blacklist )._1

  /**
   * Renames at least the eigenvariables contains in blacklist so that proof becomes regular.
   *
   * @param proof An LKProof.
   * @param blacklist A sequence of variables that must be renamed if they occur as eigenvariables.
   * @return A regular LKProof.
   */
  def apply( proof: LKProof, blacklist: Seq[Var] ): LKProof = apply_( proof, blacklist.toSet )._1

  /**
   * Performs the actual regularization.
   *
   * @param proof An LKProof.
   * @param blacklist A set of variables that must be renamed if they occur as eigenvariables.
   * @return A regular LKProof and the final blacklist.
   */
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
      val eigenNew = rename( eigen, blacklist.toList )
      val ( subProofNew_, blacklistNew ) = apply_( subProof, blacklist + eigenNew )

      val subProofNew = Substitution( eigen, eigenNew )( subProofNew_ )
      ( ForallRightRule( subProofNew, aux, eigenNew, quant ), blacklistNew )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val eigenNew = rename( eigen, blacklist.toList )
      val ( subProofNew_, blacklistNew ) = apply_( subProof, blacklist + eigenNew )

      val subProofNew = Substitution( eigen, eigenNew )( subProofNew_ )
      ( ExistsLeftRule( subProofNew, aux, eigenNew, quant ), blacklistNew )

    case ExistsRightRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( ExistsRightRule( subProofNew, aux, f, term, v ), blacklistNew )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( EqualityLeftRule( subProofNew, eq, aux, pos ), blacklistNew )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( EqualityRightRule( subProofNew, eq, aux, pos ), blacklistNew )

    case proof @ InductionRule( cases, main ) =>
      var blacklistNew = blacklist

      val newQuant = rename( proof.quant, blacklistNew.toList )
      blacklistNew += newQuant

      val newCases = cases map { c =>
        val renaming = rename( c.eigenVars.toSet, blacklistNew )
        blacklistNew ++= renaming.values
        val ( subProofNew, blacklistNew_ ) = apply_( Substitution( renaming )( c.proof ), blacklistNew )
        blacklistNew = blacklistNew_
        c.copy( proof = subProofNew, eigenVars = c.eigenVars map renaming )
      }

      InductionRule( newCases, All( newQuant, Substitution( proof.quant -> newQuant )( proof.qfFormula ) ) ) -> blacklistNew

    case DefinitionLeftRule( subProof, aux, main ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( DefinitionLeftRule( subProofNew, aux, main ), blacklistNew )

    case DefinitionRightRule( subProof, aux, main ) =>
      val ( subProofNew, blacklistNew ) = apply_( subProof, blacklist )
      ( DefinitionRightRule( subProofNew, aux, main ), blacklistNew )

    case _ => throw new IllegalArgumentException( s"This rule is not handled at this time." )
  }
}
