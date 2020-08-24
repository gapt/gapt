package gapt.proofs.lk

import gapt.proofs.SequentConnector
import gapt.proofs.gaptic.OpenAssumption
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ContractionLeftMacroRule
import gapt.proofs.lk.rules.macros.ContractionRightMacroRule

/**
 * Implementation of the visitor pattern for [[gapt.proofs.lk.LKProof]].
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
  final def apply( proof: LKProof, otherArg: T ): LKProof = withSequentConnector( proof, otherArg )._1

  /**
   * Applies the proof transformation to an LKProof.
   *
   * @param proof The input proof.
   * @return Transformed proof, and the sequent connector with the new proof as lower sequent and the old proof as upper sequent.
   */
  final def withSequentConnector( proof: LKProof, otherArg: T ): ( LKProof, SequentConnector ) = {
    val result = recurse( proof, otherArg )
    ( result._1, result._2 )
  }

  protected def recurse( proof: LKProof, otherArg: T ): ( LKProof, SequentConnector ) = proof match {
    case p: OpenAssumption =>
      visitOpenAssumption( p, otherArg )

    case p: LogicalAxiom =>
      visitLogicalAxiom( p, otherArg )

    case p: ReflexivityAxiom =>
      visitReflexivityAxiom( p, otherArg )

    case p: ProofLink =>
      visitProofLink( p, otherArg )

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

    case p: ConversionLeftRule =>
      visitDefinitionLeft( p, otherArg )

    case p: ConversionRightRule =>
      visitDefinitionRight( p, otherArg )
  }

  def transportToSubProof( arg: T, proof: LKProof, subProofIdx: Int ): T = arg

  def one2one( proof: LKProof, arg: T )( func: Seq[( LKProof, SequentConnector )] => LKProof ): ( LKProof, SequentConnector ) = {
    val visitedChildren =
      for ( ( subProof, idx ) <- proof.immediateSubProofs.zipWithIndex )
        yield recurse( subProof, transportToSubProof( arg, proof, idx ) )
    val newProof = func( visitedChildren )
    val conn = newProof.occConnectors.lazyZip( visitedChildren ).lazyZip( proof.occConnectors ).map( _ * _._2 * _.inv ).reduce( _ + _ )
    ( newProof, conn )
  }

  def withIdentitySequentConnector( proof: LKProof ): ( LKProof, SequentConnector ) =
    ( proof, SequentConnector( proof.endSequent ) )

  /*
   * Visiting methods. The implementations given here simply reconstruct the corresponding rule.
   * Different proof transformations can be implemented by overriding some of these methods.
   */

  protected def visitOpenAssumption( proof: OpenAssumption, otherArg: T ): ( LKProof, SequentConnector ) = withIdentitySequentConnector( proof )

  protected def visitLogicalAxiom( proof: LogicalAxiom, otherArg: T ): ( LKProof, SequentConnector ) = withIdentitySequentConnector( proof )

  protected def visitReflexivityAxiom( proof: ReflexivityAxiom, otherArg: T ): ( LKProof, SequentConnector ) = withIdentitySequentConnector( proof )

  protected def visitProofLink( proof: ProofLink, otherArg: T ): ( LKProof, SequentConnector ) = withIdentitySequentConnector( proof )

  protected def visitTopAxiom( otherArg: T ): ( LKProof, SequentConnector ) = withIdentitySequentConnector( TopAxiom )

  protected def visitBottomAxiom( otherArg: T ): ( LKProof, SequentConnector ) = withIdentitySequentConnector( BottomAxiom )

  protected def visitWeakeningLeft( proof: WeakeningLeftRule, otherArg: T ): ( LKProof, SequentConnector ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, transportToSubProof( otherArg, proof, 0 ) )
    val proofNew = WeakeningLeftRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv ).+( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitWeakeningRight( proof: WeakeningRightRule, otherArg: T ): ( LKProof, SequentConnector ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, transportToSubProof( otherArg, proof, 0 ) )
    val proofNew = WeakeningRightRule( subProofNew, proof.mainFormula )
    val connector = ( proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv ).+( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) )

    ( proofNew, connector )
  }

  protected def visitContractionLeft( proof: ContractionLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => ContractionLeftRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitContractionRight( proof: ContractionRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => ContractionRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitCut( proof: CutRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        CutRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitNegLeft( proof: NegLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => NegLeftRule( subProof, subConn child proof.aux ) }

  protected def visitNegRight( proof: NegRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => NegRightRule( subProof, subConn child proof.aux ) }

  protected def visitAndLeft( proof: AndLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => AndLeftRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitAndRight( proof: AndRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        AndRightRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitOrLeft( proof: OrLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        OrLeftRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitOrRight( proof: OrRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => OrRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitImpLeft( proof: ImpLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof1, subConn1 ), ( subProof2, subConn2 ) ) =>
        ImpLeftRule( subProof1, subConn1 child proof.aux1, subProof2, subConn2 child proof.aux2 )
    }

  protected def visitImpRight( proof: ImpRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { case Seq( ( subProof, subConn ) ) => ImpRightRule( subProof, subConn child proof.aux1, subConn child proof.aux2 ) }

  protected def visitForallLeft( proof: ForallLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ForallLeftRule( subProof, subConn.child( proof.aux ), proof.A, proof.term, proof.v )
    }

  protected def visitForallRight( proof: ForallRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ForallRightRule( subProof, subConn.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    }

  protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ForallSkRightRule( subProof, subConn.child( proof.aux ), proof.mainFormula, proof.skolemTerm )
    }

  protected def visitExistsLeft( proof: ExistsLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ExistsLeftRule( subProof, subConn.child( proof.aux ), proof.eigenVariable, proof.quantifiedVariable )
    }

  protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ExistsSkLeftRule( subProof, subConn.child( proof.aux ), proof.mainFormula, proof.skolemTerm )
    }

  protected def visitExistsRight( proof: ExistsRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ExistsRightRule( subProof, subConn.child( proof.aux ), proof.A, proof.term, proof.v )
    }

  protected def visitEqualityLeft( proof: EqualityLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        EqualityLeftRule( subProof, subConn.child( proof.eq ), subConn.child( proof.aux ), proof.replacementContext )
    }

  protected def visitEqualityRight( proof: EqualityRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        EqualityRightRule( subProof, subConn.child( proof.eq ), subConn.child( proof.aux ), proof.replacementContext )
    }

  protected def visitInduction( proof: InductionRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) { subProofs =>
      InductionRule(
        for ( ( c, ( subProof, subConn ) ) <- proof.cases zip subProofs )
          yield InductionCase( subProof, c.constructor, c.hypotheses map subConn.child, c.eigenVars, subConn.child( c.conclusion ) ),
        proof.formula, proof.term )
    }

  protected def visitDefinitionLeft( proof: ConversionLeftRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ConversionLeftRule( subProof, subConn.child( proof.aux ), proof.mainFormula )
    }

  protected def visitDefinitionRight( proof: ConversionRightRule, otherArg: T ): ( LKProof, SequentConnector ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProof, subConn ) ) =>
        ConversionRightRule( subProof, subConn.child( proof.aux ), proof.mainFormula )
    }

  /**
   * Transforms a visiting function by inserting contractions after it.
   * Only formula occurrences that were not in the old proof -- i.e., that have been added by the visitor -- are contracted.
   * @param visitingFunction The visiting function after which contractions should be inserted.
   *                         In most cases, just using `recurse` here should be fine.
   * @return A new visiting function that behaves the same as the old one, but contracts all duplicate new formulas at the end.
   */
  def contractAfter[A]( visitingFunction: ( LKProof, A ) => ( LKProof, SequentConnector ) ): ( LKProof, A ) => ( LKProof, SequentConnector ) = { ( proof, otherArg ) =>
    val ( subProof, subConn ) = visitingFunction( proof, otherArg )

    val newFormulas = subProof.endSequent.indicesSequent
      .filter { subConn.parents( _ ).isEmpty } // Formula occurrences that were not in the old proof
      .groupBy( subProof.endSequent( _ ) ) // Group them by formula
      .filterNot( _._2.length < 2 ) // Take only the formulas with at least two occurrences
      .map { _._2 } // Take only the indices

    val ( leftProof, leftConn ) = newFormulas.antecedent.foldLeft( ( subProof, SequentConnector( subProof.endSequent ) ) ) { ( acc, indices ) =>
      val ( p, c ) = acc
      val ( pNew, cNew ) = ContractionLeftMacroRule.withSequentConnector( p, indices map { c.child } )
      ( pNew, cNew * c )
    }

    val ( rightProof, rightConn ) = newFormulas.succedent.foldLeft( ( leftProof, leftConn ) ) { ( acc, indices ) =>
      val ( p, c ) = acc
      val ( pNew, cNew ) = ContractionRightMacroRule.withSequentConnector( p, indices map { c.child } )
      ( pNew, cNew * c )
    }

    ( rightProof, rightConn * subConn )
  }
}