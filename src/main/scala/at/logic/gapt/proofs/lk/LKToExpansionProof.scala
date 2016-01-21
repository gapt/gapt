package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.expr.{ HOLAtom, Eq }
import at.logic.gapt.proofs.Sequent
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
    val ( cuts, expansionSequent ) = extract( regularize( AtomicExpansion( proof ) ) )
    eliminateMerges( ExpansionProofWithCut( cuts, expansionSequent ) )
  }

  private def extract( proof: LKProof ): ( Seq[ETImp], Sequent[ExpansionTree] ) = proof match {

    // Axioms
    case LogicalAxiom( atom: HOLAtom ) => Seq() -> Sequent( Seq( ETAtom( atom, false ) ), Seq( ETAtom( atom, true ) ) )

    case ReflexivityAxiom( s )         => Seq() -> Sequent( Seq(), Seq( ETAtom( Eq( s, s ), true ) ) )

    case TopAxiom                      => Seq() -> Sequent( Seq(), Seq( ETTop( true ) ) )

    case BottomAxiom                   => Seq() -> Sequent( Seq( ETBottom( false ) ), Seq() )

    case TheoryAxiom( sequent )        => Seq() -> ( for ( ( a, i ) <- sequent.zipWithIndex ) yield ETAtom( a, i.isSuc ) )

    // Structural rules
    case WeakeningLeftRule( subProof, formula ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( ETWeakening( formula, false ) +: subSequent )

    case WeakeningRightRule( subProof, formula ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( subSequent :+ ETWeakening( formula, true ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 ) )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      subCuts -> ( subSequent.delete( aux1, aux2 ) :+ ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) )

    case c @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftCuts, leftSequent ) = extract( leftSubProof )
      val ( rightCuts, rightSequent ) = extract( rightSubProof )
      val newCut = ETImp( leftSequent( aux1 ), rightSequent( aux2 ) )
      val cuts = if ( containsQuantifier( c.cutFormula ) )
        newCut +: ( leftCuts ++ rightCuts )
      else leftCuts ++ rightCuts
      ( cuts, leftSequent.delete( aux1 ) ++ rightSequent.delete( aux2 ) )

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
      ( leftCuts ++ rightCuts, ( leftSubSequent ++ rightSubSequent ) :+ ETAnd( leftSubTree, rightSubTree ) )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftCuts, leftSequent ) = extract( leftSubProof )
      val ( rightCuts, rightSequent ) = extract( rightSubProof )
      val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
      ( leftCuts ++ rightCuts, ETOr( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent ) )

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

    case ExistsLeftRule( subProof, aux, eigen, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, ETStrongQuantifier( proof.mainFormulas.head, eigen, subSequent( aux ) ) +: subSequent.delete( aux ) )

    case ExistsRightRule( subProof, aux, _, t, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux ) :+ ETWeakQuantifier( proof.mainFormulas.head, Map( t -> subSequent( aux ) ) ) )

    // Equality rules
    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subCuts, sequent ) = extract( subProof )
      val ( subTree, subSequent ) = sequent.focus( aux )

      val repTerm = proof.mainFormulas.head( pos.head )
      val newTree = pos.foldLeft( subTree ) { ( acc, p ) => replaceAtHOLPosition( acc, p, repTerm ) }
      ( subCuts, newTree +: subSequent )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subCuts, sequent ) = extract( subProof )
      val ( subTree, subSequent ) = sequent.focus( aux )
      val repTerm = proof.mainFormulas.head( pos.head )
      val newTree = pos.foldLeft( subTree ) { ( acc, p ) => replaceAtHOLPosition( acc, p, repTerm ) }
      ( subCuts, subSequent :+ newTree )
  }
}
