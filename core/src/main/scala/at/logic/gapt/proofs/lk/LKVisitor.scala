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

  final def recurse( proof: LKProof, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = proof match {
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

  /*
   * Visiting methods. The implementations given here simply reconstruct the corresponding rule.
   * Different proof transformations can be implemented by overriding some of these methods.
   */

  protected def visitOpenAssumption( proof: OpenAssumption, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitLogicalAxiom( proof: LogicalAxiom, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitReflexivityAxiom( proof: ReflexivityAxiom, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitTheoryAxiom( proof: TheoryAxiom, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitTopAxiom( otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = ( TopAxiom, OccConnector( TopAxiom.endSequent ) )

  protected def visitBottomAxiom( otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = ( BottomAxiom, OccConnector( BottomAxiom.endSequent ) )

  protected def visitWeakeningLeft( proof: WeakeningLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = WeakeningLeftRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitWeakeningRight( proof: WeakeningRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = WeakeningRightRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitContractionLeft( proof: ContractionLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = ContractionLeftRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitContractionRight( proof: ContractionRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = ContractionRightRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitCut( proof: CutRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( leftSubProofNew, leftSubConnector ) = recurse( proof.leftSubProof, otherArg )
    val ( rightSubProofNew, rightSubConnector ) = recurse( proof.rightSubProof, otherArg )
    val ( aux1, aux2 ) = ( leftSubConnector.child( proof.aux1 ), rightSubConnector.child( proof.aux2 ) )
    val proofNew = CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )
    val connector = ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv )

    ( proofNew, connector )
  }

  protected def visitNegLeft( proof: NegLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = NegLeftRule( subProofNew, subConnector.child( proof.aux ) )
    ( proofNew, proofNew.getOccConnector * subConnector * proof.getOccConnector.inv )
  }

  protected def visitNegRight( proof: NegRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = NegRightRule( subProofNew, subConnector.child( proof.aux ) )
    ( proofNew, proofNew.getOccConnector * subConnector * proof.getOccConnector.inv )
  }

  protected def visitAndLeft( proof: AndLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = AndLeftRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitAndRight( proof: AndRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( leftSubProofNew, leftSubConnector ) = recurse( proof.leftSubProof, otherArg )
    val ( rightSubProofNew, rightSubConnector ) = recurse( proof.rightSubProof, otherArg )
    val proofNew = AndRightRule( leftSubProofNew, leftSubConnector.child( proof.aux1 ), rightSubProofNew, rightSubConnector.child( proof.aux2 ) )
    ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv ) )
  }

  protected def visitOrLeft( proof: OrLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( leftSubProofNew, leftSubConnector ) = recurse( proof.leftSubProof, otherArg )
    val ( rightSubProofNew, rightSubConnector ) = recurse( proof.rightSubProof, otherArg )
    val proofNew = OrLeftRule( leftSubProofNew, leftSubConnector.child( proof.aux1 ), rightSubProofNew, rightSubConnector.child( proof.aux2 ) )
    ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv ) )
  }

  protected def visitOrRight( proof: OrRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = OrRightRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitImpLeft( proof: ImpLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( leftSubProofNew, leftSubConnector ) = recurse( proof.leftSubProof, otherArg )
    val ( rightSubProofNew, rightSubConnector ) = recurse( proof.rightSubProof, otherArg )
    val proofNew = ImpLeftRule( leftSubProofNew, leftSubConnector.child( proof.aux1 ), rightSubProofNew, rightSubConnector.child( proof.aux2 ) )
    ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv ) )
  }

  protected def visitImpRight( proof: ImpRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = ImpRightRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitForallLeft( proof: ForallLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = ForallLeftRule( subProofNew, subConnector.child( proof.aux ), proof.A, proof.term, proof.v )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitForallRight( proof: ForallRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = ForallRightRule( subProofNew, subConnector.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = ForallSkRightRule( subProofNew, subConnector.child( proof.aux ), proof.mainFormula, proof.skolemTerm, proof.skolemDef )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitExistsLeft( proof: ExistsLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = ExistsLeftRule( subProofNew, subConnector.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = ExistsSkLeftRule( subProofNew, subConnector.child( proof.aux ), proof.mainFormula, proof.skolemTerm, proof.skolemDef )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitExistsRight( proof: ExistsRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = ExistsRightRule( subProofNew, subConnector.child( proof.aux ), proof.A, proof.term, proof.v )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitEqualityLeft( proof: EqualityLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = EqualityLeftRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ), proof.replacementContext )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitEqualityRight( proof: EqualityRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = EqualityRightRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ), proof.replacementContext )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitInduction( proof: InductionRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val casesConnectors = for ( c <- proof.cases ) yield {
      val ( subProofNew, subConnector ) = recurse( c.proof, otherArg )
      InductionCase( subProofNew, c.constructor, c.hypotheses map subConnector.child, c.eigenVars, subConnector.child( c.conclusion ) ) -> subConnector
    }

    val ( casesNew, subConnectors ) = casesConnectors.unzip
    val proofNew = InductionRule( casesNew, proof.mainFormula )
    val subConnectors_ = for ( ( c1, c2, c3 ) <- ( proofNew.occConnectors, subConnectors, proof.occConnectors ).zipped ) yield c1 * c2 * c3.inv
    val connector = if ( subConnectors_.isEmpty ) OccConnector( proofNew.endSequent ) else subConnectors_.reduceLeft( _ + _ )

    ( proofNew, connector )
  }

  protected def visitDefinitionLeft( proof: DefinitionLeftRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = DefinitionLeftRule( subProofNew, subConnector.child( proof.aux ), proof.main )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitDefinitionRight( proof: DefinitionRightRule, otherArg: T ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, otherArg )
    val proofNew = DefinitionRightRule( subProofNew, subConnector.child( proof.aux ), proof.main )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

}