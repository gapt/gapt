package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.gaptic.OpenAssumption

/**
 * Implementation of the visitor pattern for [[at.logic.gapt.proofs.lk.LKProof]].
 * Proof properties can check using this trait to reduce boilerplate code.
 * @tparam T Type of additional arguments that may be used in the transformation.
 */
trait LKPropVisitor[T] {
  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return Boolean concerning the property being checked.
   */
  final def apply( proof: LKProof, otherArg: T ): Boolean = recurse( proof, otherArg )

  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return A pair consisting of the transformed proof and an SequentConnector relating the two proofs.
   */

  protected def recurse( proof: LKProof, otherArg: T ): Boolean = proof match {
    case p: OpenAssumption       => visitOpenAssumption( p, otherArg )
    case p: LogicalAxiom         => visitLogicalAxiom( p, otherArg )
    case p: ReflexivityAxiom     => visitReflexivityAxiom( p, otherArg )
    case p: ProofLink            => visitProofLink( p, otherArg )
    case TopAxiom                => visitTopAxiom( otherArg )
    case BottomAxiom             => visitBottomAxiom( otherArg )
    case p: WeakeningLeftRule    => visitWeakeningLeft( p, otherArg )
    case p: WeakeningRightRule   => visitWeakeningRight( p, otherArg )
    case p: ContractionLeftRule  => visitContractionLeft( p, otherArg )
    case p: ContractionRightRule => visitContractionRight( p, otherArg )
    case p: CutRule              => visitCut( p, otherArg )
    case p: NegLeftRule          => visitNegLeft( p, otherArg )
    case p: NegRightRule         => visitNegRight( p, otherArg )
    case p: AndLeftRule          => visitAndLeft( p, otherArg )
    case p: AndRightRule         => visitAndRight( p, otherArg )
    case p: OrLeftRule           => visitOrLeft( p, otherArg )
    case p: OrRightRule          => visitOrRight( p, otherArg )
    case p: ImpLeftRule          => visitImpLeft( p, otherArg )
    case p: ImpRightRule         => visitImpRight( p, otherArg )
    case p: ForallLeftRule       => visitForallLeft( p, otherArg )
    case p: ForallRightRule      => visitForallRight( p, otherArg )
    case p: ForallSkRightRule    => visitForallSkRight( p, otherArg )
    case p: ExistsLeftRule       => visitExistsLeft( p, otherArg )
    case p: ExistsSkLeftRule     => visitExistsSkLeft( p, otherArg )
    case p: ExistsRightRule      => visitExistsRight( p, otherArg )
    case p: EqualityLeftRule     => visitEqualityLeft( p, otherArg )
    case p: EqualityRightRule    => visitEqualityRight( p, otherArg )
    case p: InductionRule        => visitInduction( p, otherArg )
    case p: DefinitionLeftRule   => visitDefinitionLeft( p, otherArg )
    case p: DefinitionRightRule  => visitDefinitionRight( p, otherArg )
  }

  def joinProp( proof: LKProof, arg: T ): Boolean = {
    val visitedChildren = for ( ( subProof, idx ) <- proof.immediateSubProofs.zipWithIndex ) yield recurse( subProof, arg )
    visitedChildren.fold( true ) { ( a, b ) => a & b }
  }

  /*
   * Visiting methods. The implementations given here simply reconstruct the corresponding rule.
   * Different proof transformations can be implemented by overriding some of these methods.
   */

  protected def visitOpenAssumption( proof: OpenAssumption, otherArg: T ): Boolean = true
  protected def visitLogicalAxiom( proof: LogicalAxiom, otherArg: T ): Boolean = true
  protected def visitReflexivityAxiom( proof: ReflexivityAxiom, otherArg: T ): Boolean = true
  protected def visitProofLink( proof: ProofLink, otherArg: T ): Boolean = true
  protected def visitTopAxiom( otherArg: T ): Boolean = true
  protected def visitBottomAxiom( otherArg: T ): Boolean = true
  protected def visitWeakeningLeft( proof: WeakeningLeftRule, otherArg: T ): Boolean = recurse( proof.subProof, otherArg )
  protected def visitWeakeningRight( proof: WeakeningRightRule, otherArg: T ): Boolean = recurse( proof.subProof, otherArg )
  protected def visitContractionLeft( proof: ContractionLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitContractionRight( proof: ContractionRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitCut( proof: CutRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitNegLeft( proof: NegLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitNegRight( proof: NegRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitAndLeft( proof: AndLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitAndRight( proof: AndRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitOrLeft( proof: OrLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitOrRight( proof: OrRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitImpLeft( proof: ImpLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitImpRight( proof: ImpRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitForallLeft( proof: ForallLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitForallRight( proof: ForallRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitExistsLeft( proof: ExistsLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitExistsRight( proof: ExistsRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitEqualityLeft( proof: EqualityLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitEqualityRight( proof: EqualityRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitInduction( proof: InductionRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitDefinitionLeft( proof: DefinitionLeftRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
  protected def visitDefinitionRight( proof: DefinitionRightRule, otherArg: T ): Boolean = joinProp( proof, otherArg )
}