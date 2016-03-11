package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ OccConnector, Sequent, SequentIndex }

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
    case InductionRule( cases, main ) =>
      freeVariables( p.conclusion ) ++ ( cases flatMap { c =>
        apply( c.proof ) -- c.eigenVars
      } )
    case _ =>
      freeVariables( p.conclusion ) ++ p.immediateSubProofs.flatMap( apply )
  }
}

object groundFreeVarsLK {
  def apply( p: LKProof ): LKProof =
    Substitution( freeVariablesLK( p ) map {
      case v @ Var( n, t ) => v -> Const( n, t )
    } )( p )
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
object regularize extends LKVisitor[Set[Var]] {
  /**
   * Renames all eigenvariables in a proof so that it becomes regular.
   *
   * @param proof An LKProof.
   * @return A regular LKProof.
   */
  def apply( proof: LKProof ): LKProof = apply( proof, freeVariablesLK( proof ) )

  /**
   * Renames at least the eigenvariables contains in blacklist so that proof becomes regular.
   *
   * @param proof An LKProof.
   * @param blacklist A sequence of variables that must be renamed if they occur as eigenvariables.
   * @return A regular LKProof.
   */
  def apply( proof: LKProof, blacklist: Seq[Var] ): LKProof = apply( proof, blacklist.toSet )

  protected override def visitForallRight( proof: ForallRightRule, blacklist: Set[Var] ) = {
    val ForallRightRule( subProof, aux, eigen, quant ) = proof
    val eigenNew = rename( eigen, blacklist )
    val ( subProofNew_, subConnector, blacklistNew ) = recurse( subProof, blacklist + eigenNew )

    val subProofNew = Substitution( eigen, eigenNew )( subProofNew_ )
    val proofNew = ForallRightRule( subProofNew, aux, eigenNew, quant )
    ( proofNew, proofNew.getOccConnector * subConnector * proof.getOccConnector.inv, blacklistNew )
  }

  protected override def visitExistsLeft( proof: ExistsLeftRule, blacklist: Set[Var] ) = {
    val ExistsLeftRule( subProof, aux, eigen, quant ) = proof
    val eigenNew = rename( eigen, blacklist )
    val ( subProofNew_, subConnector, blacklistNew ) = recurse( subProof, blacklist + eigenNew )

    val subProofNew = Substitution( eigen, eigenNew )( subProofNew_ )
    val proofNew = ExistsLeftRule( subProofNew, aux, eigenNew, quant )
    ( proofNew, proofNew.getOccConnector * subConnector * proof.getOccConnector.inv, blacklistNew )
  }

  protected override def visitInduction( proof: InductionRule, blacklist: Set[Var] ) = {
    val InductionRule( cases, main ) = proof
    var blacklistNew = blacklist

    val newQuant = rename( proof.quant, blacklistNew )
    blacklistNew += newQuant

    val newCasesConnectors = cases map { c =>
      val renaming = rename( c.eigenVars, blacklistNew )
      blacklistNew ++= renaming.values
      val ( subProofNew, subConnector, blacklistNew_ ) = recurse( Substitution( renaming )( c.proof ), blacklistNew )
      blacklistNew = blacklistNew_
      c.copy( proof = subProofNew, eigenVars = c.eigenVars map renaming ) -> subConnector
    }

    val ( casesNew, subConnectors ) = newCasesConnectors.unzip
    val proofNew = InductionRule( casesNew, proof.mainFormula )
    val subConnectors_ = for ( ( c1, c2, c3 ) <- ( proofNew.occConnectors, subConnectors, proof.occConnectors ).zipped ) yield c1 * c2 * c3.inv
    val connector = if ( subConnectors_.isEmpty ) OccConnector( proofNew.endSequent ) else subConnectors_.reduceLeft( _ + _ )

    ( proofNew, connector, blacklistNew )
  }

}
