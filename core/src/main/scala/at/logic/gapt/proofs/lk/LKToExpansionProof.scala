package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.hol.{ containsQuantifierOnLogicalLevel, instantiate }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, SequentIndex }
import at.logic.gapt.proofs.expansion._

object LKToExpansionProof {

  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   *
   * The induction rule is not supported!
   *
   * @param proof The proof π.
   * @return The expansion proof Ex(π).
   */
  def apply( proof: LKProof ): ExpansionProofWithCut = {
    val ( theory, expansionSequent ) = extract( regularize( AtomicExpansion( proof ) ) )
    val theory_ = theory.groupBy { _.shallow }.values.toSeq.map { ETMerge( _ ) }
    eliminateMerges( ExpansionProofWithCut( theory_ ++: expansionSequent ) )
  }

  private def extract( proof: LKProof ): ( Seq[ExpansionTree], Sequent[ExpansionTree] ) = proof match {

    // Axioms
    case LogicalAxiom( atom: HOLAtom ) => Seq() -> Sequent( Seq( ETAtom( atom, Polarity.InAntecedent ) ), Seq( ETAtom( atom, Polarity.InSuccedent ) ) )

    case ReflexivityAxiom( s )         => Seq() -> Sequent( Seq(), Seq( ETAtom( Eq( s, s ), Polarity.InSuccedent ) ) )

    case TopAxiom                      => Seq() -> Sequent( Seq(), Seq( ETTop( Polarity.InSuccedent ) ) )

    case BottomAxiom                   => Seq() -> Sequent( Seq( ETBottom( Polarity.InAntecedent ) ), Seq() )

    case TheoryAxiom( sequent )        => Seq() -> ( for ( ( a, i ) <- sequent.zipWithIndex ) yield ETAtom( a, i.polarity ) )

    // Structural rules
    case WeakeningLeftRule( subProof, formula ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( ETWeakening( formula, Polarity.InAntecedent ) +: subSequent )

    case WeakeningRightRule( subProof, formula ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( subSequent :+ ETWeakening( formula, Polarity.InSuccedent ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 ) )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( subSequent.delete( aux1, aux2 ) :+ ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) )

    case c @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftCuts, leftSequent ) = extract( leftSubProof )
      val ( rightCuts, rightSequent ) = extract( rightSubProof )
      val newCut = ETWeakQuantifier(
        ExpansionProofWithCut.cutAxiom,
        Map( c.cutFormula -> ETImp( leftSequent( aux1 ), rightSequent( aux2 ) ) )
      )
      val cuts = if ( containsQuantifierOnLogicalLevel( c.cutFormula ) )
        newCut +: ( leftCuts ++ rightCuts )
      else leftCuts ++ rightCuts
      cuts -> ( leftSequent.delete( aux1 ) ++ rightSequent.delete( aux2 ) )

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( ETNeg( subSequent( aux ) ) +: subSequent.delete( aux ) )

    case NegRightRule( subProof, aux ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( subSequent.delete( aux ) :+ ETNeg( subSequent( aux ) ) )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( ETAnd( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 ) )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftCuts, leftSequent ) = extract( leftSubProof )
      val ( rightCuts, rightSequent ) = extract( rightSubProof )
      val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
      ( leftCuts ++ rightCuts ) -> ( leftSubSequent ++ rightSubSequent :+ ETAnd( leftSubTree, rightSubTree ) )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftCuts, leftSequent ) = extract( leftSubProof )
      val ( rightCuts, rightSequent ) = extract( rightSubProof )
      val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
      ( leftCuts ++ rightCuts ) -> ( ETOr( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent ) )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( subSequent.delete( aux1, aux2 ) :+ ETOr( subSequent( aux1 ), subSequent( aux2 ) ) )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftCuts, leftSequent ) = extract( leftSubProof )
      val ( rightCuts, rightSequent ) = extract( rightSubProof )
      val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
      ( leftCuts ++ rightCuts, ETImp( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent ) )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux1, aux2 ) :+ ETImp( subSequent( aux1 ), subSequent( aux2 ) ) )

    // Quantifier rules
    case ForallLeftRule( subProof, aux, _, t, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, ETWeakQuantifier( proof.mainFormulas.head, Map( t -> subSequent( aux ) ) ) +: subSequent.delete( aux ) )

    case ForallRightRule( subProof, aux, eigen, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux ) :+ ETStrongQuantifier( proof.mainFormulas.head, eigen, subSequent( aux ) ) )

    case ForallSkRightRule( subProof, aux, main, skT, skD ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux ) :+ ETSkolemQuantifier( main, skT, skD, subSequent( aux ) ) )

    case ExistsLeftRule( subProof, aux, eigen, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, ETStrongQuantifier( proof.mainFormulas.head, eigen, subSequent( aux ) ) +: subSequent.delete( aux ) )

    case ExistsSkLeftRule( subProof, aux, main, skT, skD ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, ETSkolemQuantifier( main, skT, skD, subSequent( aux ) ) +: subSequent.delete( aux ) )

    case ExistsRightRule( subProof, aux, _, t, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux ) :+ ETWeakQuantifier( proof.mainFormulas.head, Map( t -> subSequent( aux ) ) ) )

    // Equality rules
    case p: EqualityRule =>
      val ( subCuts, sequent ) = extract( p.subProof )
      val auxTree = sequent( p.aux )

      val newAuxTree = replaceWithContext( auxTree, p.replacementContext, p.by )
      val newEqTree = ETMerge( ETAtom( p.subProof.conclusion( p.eq ).asInstanceOf[HOLAtom], Polarity.InAntecedent ), sequent( p.eq ) )
      val context = sequent.updated( p.eq, newEqTree ).delete( p.aux )
      ( subCuts, if ( p.aux.isAnt ) newAuxTree +: context else context :+ newAuxTree )

    case p: DefinitionRule =>
      val ( subCuts, subSequent ) = extract( p.subProof )

      subCuts -> subSequent.modify( p.aux ) {
        insertDefinition( _, p.definition, p.replacementContext )
      }
  }
}