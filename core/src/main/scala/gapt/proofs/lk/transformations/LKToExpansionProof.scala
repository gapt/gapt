package gapt.proofs.lk.transformations

import gapt.expr.Atom
import gapt.expr.Eq
import gapt.expr.Polarity
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.expansion.ETAnd
import gapt.proofs.expansion.ETAtom
import gapt.proofs.expansion.ETBottom
import gapt.proofs.expansion.ETCut
import gapt.proofs.expansion.ETDefinition
import gapt.proofs.expansion.ETImp
import gapt.proofs.expansion.ETMerge
import gapt.proofs.expansion.ETNeg
import gapt.proofs.expansion.ETOr
import gapt.proofs.expansion.ETSkolemQuantifier
import gapt.proofs.expansion.ETStrongQuantifier
import gapt.proofs.expansion.ETTop
import gapt.proofs.expansion.ETWeakQuantifier
import gapt.proofs.expansion.ETWeakening
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.expansion.ExpansionTree
import gapt.proofs.expansion.eliminateMerges
import gapt.proofs.expansion.isPropositionalET
import gapt.proofs.expansion.moveDefsUpward
import gapt.proofs.expansion.replaceWithContext
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
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
import gapt.proofs.lk.util.AtomicExpansion
import gapt.proofs.lk.util.regularize

object LKToExpansionProof {

  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   *
   * @param proof The proof π.
   * @return The expansion proof Ex(π).
   */
  def apply( proof: LKProof )( implicit ctx: Context = Context() ): ExpansionProof = {
    val ( theory, expansionSequent ) = extract( regularize( AtomicExpansion( makeInductionExplicit( proof ) ) ) )
    val theory_ = ETMerge.byShallowFormula( theory )
    eliminateMerges( moveDefsUpward( ExpansionProof( theory_ ++: expansionSequent ) ) )
  }
  def withoutMerge( proof: LKProof )( implicit ctx: Context = Context() ): ExpansionProof = {
    val ( theory, expansionSequent ) = extract( regularize( AtomicExpansion( makeInductionExplicit( proof ) ) ) )
    moveDefsUpward( ExpansionProof( theory ++: expansionSequent ) )
  }

  private def extract( proof: LKProof )( implicit ctx: Context ): ( Seq[ExpansionTree], Sequent[ExpansionTree] ) = proof match {

    // Axioms
    case LogicalAxiom( atom: Atom ) => Seq() -> Sequent( Seq( ETAtom( atom, Polarity.InAntecedent ) ), Seq( ETAtom( atom, Polarity.InSuccedent ) ) )

    case ReflexivityAxiom( s )      => Seq() -> Sequent( Seq(), Seq( ETAtom( Eq( s, s ), Polarity.InSuccedent ) ) )

    case TopAxiom                   => Seq() -> Sequent( Seq(), Seq( ETTop( Polarity.InSuccedent ) ) )

    case BottomAxiom                => Seq() -> Sequent( Seq( ETBottom( Polarity.InAntecedent ) ), Seq() )

    case ProofLink( _, sequent ) =>
      Seq() -> ( for ( ( a, i ) <- sequent.zipWithIndex )
        yield ETAtom( a.asInstanceOf[Atom], i.polarity ) )

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
      val tree1 = leftSequent( aux1 )
      val tree2 = rightSequent( aux2 )
      val cuts =
        if ( isPropositionalET( tree1 ) && isPropositionalET( tree2 ) )
          leftCuts ++ rightCuts
        else
          ETCut( tree1, tree2 ) +: ( leftCuts ++ rightCuts )
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

    case ForallSkRightRule( subProof, aux, main, skT ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux ) :+ ETSkolemQuantifier( main, skT, subSequent( aux ) ) )

    case ExistsLeftRule( subProof, aux, eigen, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, ETStrongQuantifier( proof.mainFormulas.head, eigen, subSequent( aux ) ) +: subSequent.delete( aux ) )

    case ExistsSkLeftRule( subProof, aux, main, skT ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, ETSkolemQuantifier( main, skT, subSequent( aux ) ) +: subSequent.delete( aux ) )

    case ExistsRightRule( subProof, aux, _, t, _ ) =>
      val ( subCuts, subSequent ) = extract( subProof )
      ( subCuts, subSequent.delete( aux ) :+ ETWeakQuantifier( proof.mainFormulas.head, Map( t -> subSequent( aux ) ) ) )

    // Equality rules
    case p: EqualityRule =>
      val ( subCuts, sequent ) = extract( p.subProof )
      val auxTree = sequent( p.aux )

      val newAuxTree = replaceWithContext( auxTree, p.replacementContext, p.by )
      val newEqTree = ETMerge( ETAtom( p.subProof.conclusion( p.eq ).asInstanceOf[Atom], Polarity.InAntecedent ), sequent( p.eq ) )
      val context = sequent.updated( p.eq, newEqTree ).delete( p.aux )
      ( subCuts, if ( p.aux.isAnt ) newAuxTree +: context else context :+ newAuxTree )

    case ConversionLeftRule( subProof, aux, main ) =>
      val ( subCuts, subSequent ) = extract( subProof )

      ( subCuts, ETDefinition( main, subSequent( aux ) ) +: subSequent.delete( aux ) )

    case ConversionRightRule( subProof, aux, main ) =>
      val ( subCuts, subSequent ) = extract( subProof )

      ( subCuts, subSequent.delete( aux ) :+ ETDefinition( main, subSequent( aux ) ) )

    case p @ InductionRule( _, _, _ ) =>
      // TODO: remove makeInductionExplicit and construct expansion tree here
      ???
  }
}
