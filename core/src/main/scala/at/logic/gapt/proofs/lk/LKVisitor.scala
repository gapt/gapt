package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.OccConnector

/**
 * Created by sebastian on 3/10/16.
 */

/**
 * Implementation of the visitor pattern for [[at.logic.gapt.proofs.lk.LKProof]].
 * Proof transformations can implement this trait to reduce boilerplate code.
 */
trait LKVisitor {
  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return The transformed proof.
   */
  final def apply( proof: LKProof ): LKProof = withOccConnector( proof )._1

  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return A pair consisting of the transformed proof and an OccConnector relating the two proofs.
   */
  final def withOccConnector( proof: LKProof ): ( LKProof, OccConnector[HOLFormula] ) = matchSubproof( proof )

  /**
   * Case distinction on subproofs that calls the appropriate visiting methods.
   *
   */
  protected final def matchSubproof( proof: LKProof ): ( LKProof, OccConnector[HOLFormula] ) = proof match {
    case p: LogicalAxiom =>
      visitLogicalAxiom( p )

    case p: ReflexivityAxiom =>
      visitReflexivityAxiom( p )

    case p: TheoryAxiom =>
      visitTheoryAxiom( p )

    case TopAxiom =>
      visitTopAxiom

    case BottomAxiom =>
      visitBottomAxiom

    case p: WeakeningLeftRule =>
      visitWeakeningLeft( p )

    case p: WeakeningRightRule =>
      visitWeakeningRight( p )

    case p: ContractionLeftRule =>
      visitContractionLeft( p )

    case p: ContractionRightRule =>
      visitContractionRight( p )

    case p: CutRule =>
      visitCut( p )

    case p: NegLeftRule =>
      visitNegLeft( p )

    case p: NegRightRule =>
      visitNegRight( p )

    case p: AndLeftRule =>
      visitAndLeft( p )

    case p: AndRightRule =>
      visitAndRight( p )

    case p: OrLeftRule =>
      visitOrLeft( p )

    case p: OrRightRule =>
      visitOrRight( p )

    case p: ImpLeftRule =>
      visitImpLeft( p )

    case p: ImpRightRule =>
      visitImpRight( p )

    case p: ForallLeftRule =>
      visitForallLeft( p )

    case p: ForallRightRule =>
      visitForallRight( p )

    case p: ExistsLeftRule =>
      visitExistsLeft( p )

    case p: ExistsRightRule =>
      visitExistsRight( p )

    case p: EqualityLeftRule =>
      visitEqualityLeft( p )

    case p: EqualityRightRule =>
      visitEqualityRight( p )

    case p: InductionRule =>
      visitInduction( p )

    case p: DefinitionLeftRule =>
      visitDefinitionLeft( p )

    case p: DefinitionRightRule =>
      visitDefinitionRight( p )
  }

  /*
   * Visiting methods. The implementations given here simply reconstruct the corresponding rule.
   * Different proof transformations can be implemented by overriding some of these methods.
   */

  protected def visitLogicalAxiom( proof: LogicalAxiom ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitReflexivityAxiom( proof: ReflexivityAxiom ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitTheoryAxiom( proof: TheoryAxiom ): ( LKProof, OccConnector[HOLFormula] ) = ( proof, OccConnector( proof.endSequent ) )

  protected def visitTopAxiom: ( LKProof, OccConnector[HOLFormula] ) = ( TopAxiom, OccConnector( TopAxiom.endSequent ) )

  protected def visitBottomAxiom: ( LKProof, OccConnector[HOLFormula] ) = ( BottomAxiom, OccConnector( BottomAxiom.endSequent ) )

  protected def visitWeakeningLeft( proof: WeakeningLeftRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = WeakeningLeftRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitWeakeningRight( proof: WeakeningRightRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = WeakeningRightRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitContractionLeft( proof: ContractionLeftRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = ContractionLeftRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitContractionRight( proof: ContractionRightRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = ContractionRightRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitCut( proof: CutRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( leftSubProofNew, leftSubConnector ) = matchSubproof( proof.leftSubProof )
    val ( rightSubProofNew, rightSubConnector ) = matchSubproof( proof.rightSubProof )
    val ( aux1, aux2 ) = ( leftSubConnector.child( proof.aux1 ), rightSubConnector.child( proof.aux2 ) )
    val proofNew = CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )
    val connector = ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv )

    ( proofNew, connector )
  }

  protected def visitNegLeft( proof: NegLeftRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = NegLeftRule( subProofNew, subConnector.child( proof.aux ) )
    ( proofNew, proofNew.getOccConnector * subConnector * proof.getOccConnector.inv )
  }

  protected def visitNegRight( proof: NegRightRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = NegRightRule( subProofNew, subConnector.child( proof.aux ) )
    ( proofNew, proofNew.getOccConnector * subConnector * proof.getOccConnector.inv )
  }

  protected def visitAndLeft( proof: AndLeftRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = AndLeftRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitAndRight( proof: AndRightRule ) = {
    val ( leftSubProofNew, leftSubConnector ) = matchSubproof( proof.leftSubProof )
    val ( rightSubProofNew, rightSubConnector ) = matchSubproof( proof.rightSubProof )
    val proofNew = AndRightRule( leftSubProofNew, leftSubConnector.child( proof.aux1 ), rightSubProofNew, rightSubConnector.child( proof.aux2 ) )
    ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv ) )
  }

  protected def visitOrLeft( proof: OrLeftRule ) = {
    val ( leftSubProofNew, leftSubConnector ) = matchSubproof( proof.leftSubProof )
    val ( rightSubProofNew, rightSubConnector ) = matchSubproof( proof.rightSubProof )
    val proofNew = OrLeftRule( leftSubProofNew, leftSubConnector.child( proof.aux1 ), rightSubProofNew, rightSubConnector.child( proof.aux2 ) )
    ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv ) )
  }

  protected def visitOrRight( proof: OrRightRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = OrRightRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitImpLeft( proof: ImpLeftRule ) = {
    val ( leftSubProofNew, leftSubConnector ) = matchSubproof( proof.leftSubProof )
    val ( rightSubProofNew, rightSubConnector ) = matchSubproof( proof.rightSubProof )
    val proofNew = ImpLeftRule( leftSubProofNew, leftSubConnector.child( proof.aux1 ), rightSubProofNew, rightSubConnector.child( proof.aux2 ) )
    ( proofNew, ( proofNew.getLeftOccConnector * leftSubConnector * proof.getLeftOccConnector.inv ) + ( proofNew.getRightOccConnector * rightSubConnector * proof.getRightOccConnector.inv ) )
  }

  protected def visitImpRight( proof: ImpRightRule ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val List( aux1, aux2 ) = proof.auxIndices( 0 ) map subConnector.child
    val proofNew = ImpRightRule( subProofNew, aux1, aux2 )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitForallLeft( proof: ForallLeftRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = ForallLeftRule( subProofNew, subConnector.child( proof.aux ), proof.A, proof.term, proof.v )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitForallRight( proof: ForallRightRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = ForallRightRule( subProofNew, subConnector.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitExistsLeft( proof: ExistsLeftRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = ExistsLeftRule( subProofNew, subConnector.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitExistsRight( proof: ExistsRightRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = ExistsRightRule( subProofNew, subConnector.child( proof.aux ), proof.A, proof.term, proof.v )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitEqualityLeft( proof: EqualityLeftRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = EqualityLeftRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ), proof.positions )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitEqualityRight( proof: EqualityRightRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = EqualityRightRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ), proof.positions )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitInduction( proof: InductionRule ) = {
    val casesConnectors = for ( c <- proof.cases ) yield {
      val ( subProofNew, subConnector ) = matchSubproof( c.proof )
      InductionCase( subProofNew, c.constructor, c.hypotheses map subConnector.child, c.eigenVars, subConnector.child( c.conclusion ) ) -> subConnector
    }

    val ( casesNew, subConnectors ) = casesConnectors.unzip
    val proofNew = InductionRule( casesNew, proof.mainFormula )
    val subConnectors_ = for ( ( c1, c2, c3 ) <- ( proofNew.occConnectors, subConnectors, proof.occConnectors ).zipped ) yield c1 * c2 * c3.inv
    val connector = if ( subConnectors_.isEmpty ) OccConnector( proofNew.endSequent ) else subConnectors_.reduceLeft( _ + _ )

    proofNew -> connector
  }

  protected def visitDefinitionLeft( proof: DefinitionLeftRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = DefinitionLeftRule( subProofNew, subConnector.child( proof.aux ), proof.main )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

  protected def visitDefinitionRight( proof: DefinitionRightRule ) = {
    val ( subProofNew, subConnector ) = matchSubproof( proof.subProof )
    val proofNew = DefinitionRightRule( subProofNew, subConnector.child( proof.aux ), proof.main )
    val connector = proofNew.getOccConnector * subConnector * proof.getOccConnector.inv

    ( proofNew, connector )
  }

}