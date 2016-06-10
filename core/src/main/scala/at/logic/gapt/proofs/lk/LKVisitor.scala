package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.OccConnector
import at.logic.gapt.proofs.gaptic.OpenAssumption

/**
 * Implementation of the visitor pattern for [[at.logic.gapt.proofs.lk.LKProof]].
 * Proof transformations can implement this trait to reduce boilerplate code.
 * @tparam T Type of additional arguments that may be used in the transformation.
 */
trait LKVisitor[T] {
  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return The transformed proof.
   */
  final def apply( proof: LKProof, otherArg: T ): LKProof = withOccConnector( proof, otherArg )._1

  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return A pair consisting of the transformed proof and an OccConnector relating the two proofs.
   */
  final def withOccConnector( proof: LKProof, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val result = recurse( proof, otherArg )
    ( result._1, result._2 )
  }

  def recurse( proof: LKProof, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = proof match {
    case p: OpenAssumption =>
      visitOpenAssumption( p, otherArg )

    case p: LogicalAxiom =>
      visitLogicalAxiom( p, otherArg )

    case p: ReflexivityAxiom =>
      visitReflexivityAxiom( p, otherArg )

    case p: TheoryAxiom =>
      visitTheoryAxiom( p, otherArg )

    case TopAxiom =>
      visitTopAxiom( otherArg )

    case BottomAxiom =>
      visitBottomAxiom( otherArg )

    case p: WeakeningLeftRule =>
      visitWeakeningLeft( p, otherArg )

    case p: WeakeningRightRule =>
      visitWeakeningRight( p, otherArg )

    case p: ContractionLeftRule =>
      visitContractionLeft( p, otherArg )

    case p: ContractionRightRule =>
      visitContractionRight( p, otherArg )

    case p: CutRule =>
      visitCut( p, otherArg )

    case p: NegLeftRule =>
      visitNegLeft( p, otherArg )

    case p: NegRightRule =>
      visitNegRight( p, otherArg )

    case p: AndLeftRule =>
      visitAndLeft( p, otherArg )

    case p: AndRightRule =>
      visitAndRight( p, otherArg )

    case p: OrLeftRule =>
      visitOrLeft( p, otherArg )

    case p: OrRightRule =>
      visitOrRight( p, otherArg )

    case p: ImpLeftRule =>
      visitImpLeft( p, otherArg )

    case p: ImpRightRule =>
      visitImpRight( p, otherArg )

    case p: ForallLeftRule =>
      visitForallLeft( p, otherArg )

    case p: ForallRightRule =>
      visitForallRight( p, otherArg )

    case p: ForallSkRightRule =>
      visitForallSkRight( p, otherArg )

    case p: ExistsLeftRule =>
      visitExistsLeft( p, otherArg )

    case p: ExistsSkLeftRule =>
      visitExistsSkLeft( p, otherArg )

    case p: ExistsRightRule =>
      visitExistsRight( p, otherArg )

    case p: EqualityLeftRule =>
      visitEqualityLeft( p, otherArg )

    case p: EqualityRightRule =>
      visitEqualityRight( p, otherArg )

    case p: InductionRule =>
      visitInduction( p, otherArg )

    case p: DefinitionLeftRule =>
      visitDefinitionLeft( p, otherArg )

    case p: DefinitionRightRule =>
      visitDefinitionRight( p, otherArg )
  }

  def transportToSubProof( arg: T, proof: LKProof, subProofIdx: Int ): T = arg

  def one2one( proof: LKProof, arg: T )( func: Seq[( LKProof, OccConnector[HOLFormula] )] => LKProof ): ( LKProof, OccConnector[HOLFormula] ) = {
    val visitedChildren =
      for ( ( subProof, idx ) <- proof.immediateSubProofs.zipWithIndex )
        yield recurse( subProof, transportToSubProof( arg, proof, idx ) )
    val newProof = func( visitedChildren )
    val conn = ( newProof.occConnectors, visitedChildren, proof.occConnectors ).zipped.map( _ * _._2 * _.inv ).reduce( _ + _ )
    ( newProof, conn )
  }

  def withIdentityOccConnector( proof: LKProof ): ( LKProof, OccConnector[HOLFormula] ) =
    ( proof, OccConnector( proof.endSequent ) )

  /*
   * Visiting methods. The implementations given here simply reconstruct the corresponding rule.
   * Different proof transformations can be implemented by overriding some of these methods.
   */

  protected def visitOpenAssumption( proof: OpenAssumption, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = withIdentityOccConnector( proof )

  protected def visitLogicalAxiom( proof: LogicalAxiom, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = withIdentityOccConnector( proof )

  protected def visitReflexivityAxiom( proof: ReflexivityAxiom, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = withIdentityOccConnector( proof )

  protected def visitTheoryAxiom( proof: TheoryAxiom, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = withIdentityOccConnector( proof )

  protected def visitTopAxiom( otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = withIdentityOccConnector( TopAxiom )

  protected def visitBottomAxiom( otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = withIdentityOccConnector( BottomAxiom )

  protected def visitWeakeningLeft( proof: WeakeningLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, transportToSubProof( otherArg, proof, 0 ) )
    val proofNew = WeakeningLeftRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitWeakeningRight( proof: WeakeningRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, transportToSubProof( otherArg, proof, 0 ) )
    val proofNew = WeakeningRightRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitContractionLeft( proof: ContractionLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => ContractionLeftRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitContractionRight( proof: ContractionRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => ContractionRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitCut( proof: CutRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        CutRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitNegLeft( proof: NegLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => NegLeftRule( subProof, subConn child proof.aux ) }

  protected def visitNegRight( proof: NegRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => NegRightRule( subProof, subConn child proof.aux ) }

  protected def visitAndLeft( proof: AndLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => AndLeftRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitAndRight( proof: AndRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        AndRightRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitOrLeft( proof: OrLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        OrLeftRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitOrRight( proof: OrRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => OrRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitImpLeft( proof: ImpLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        ImpLeftRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitImpRight( proof: ImpRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => ImpRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitForallLeft( proof: ForallLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ForallLeftRule( subProof, subConn.child( proof.aux ), proof.A, proof.term, proof.v )
    }

  protected def visitForallRight( proof: ForallRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ForallRightRule( subProof, subConn.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    }

  protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ForallSkRightRule( subProof, subConn.child( proof.aux ), proof.mainFormula, proof.skolemTerm, proof.skolemDef )
    }

  protected def visitExistsLeft( proof: ExistsLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ExistsLeftRule( subProof, subConn.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    }

  protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ExistsSkLeftRule( subProof, subConn.child( proof.aux ), proof.mainFormula, proof.skolemTerm, proof.skolemDef )
    }

  protected def visitExistsRight( proof: ExistsRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ExistsRightRule( subProof, subConn.child( proof.aux ), proof.A, proof.term, proof.v )
    }

  protected def visitEqualityLeft( proof: EqualityLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        EqualityLeftRule( subProof, subConn.child( proof.eq ), subConn.child( proof.aux ), proof.replacementContext )
    }

  protected def visitEqualityRight( proof: EqualityRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        EqualityRightRule( subProof, subConn.child( proof.eq ), subConn.child( proof.aux ), proof.replacementContext )
    }

  protected def visitInduction( proof: InductionRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case subProofs =>
        InductionRule(
          for ( ( c, ( subProof, subConn ) ) <- proof.cases zip subProofs )
            yield InductionCase( subProof, c.constructor, c.hypotheses map subConn.child, c.eigenVars, subConn.child( c.conclusion ) ),
          proof.mainFormula
        )
    }

  protected def visitDefinitionLeft( proof: DefinitionLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        DefinitionLeftRule( subProof, subConn.child( proof.aux ), proof.main )
    }

  protected def visitDefinitionRight( proof: DefinitionRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        DefinitionRightRule( subProof, subConn.child( proof.aux ), proof.main )
    }

}