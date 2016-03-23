package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr.hol.{ HOLPosition, containsQuantifier, containsQuantifierOnLogicalLevel }
import at.logic.gapt.expr.{ Eq, HOLAtom }
import at.logic.gapt.proofs.{ Ant, Sequent, Suc }
import at.logic.gapt.proofs.expansion._

object LKskToExpansionProof {

  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   *
   * The induction rule is not supported!
   *
   * @param proof The proof π.
   * @return The expansion proof Ex(π).
   */
  def apply( proof: LKskProof ): ExpansionProofWithCut = {
    val ( cuts, expansionSequent ) = extract( proof )
    eliminateMerges( ExpansionProofWithCut( cuts, expansionSequent ) )
  }

  private def extract( proof: LKskProof ): ( Seq[ETImp], Sequent[ExpansionTree] ) = {
    val r = proof match {

      // Axioms
      case Axiom( l_ant, l_suc, atom: HOLAtom ) => Seq() -> Sequent( Seq( ETAtom( atom, false ) ), Seq( ETAtom( atom, true ) ) )

      case Reflexivity( l, s )                  => Seq() -> Sequent( Seq(), Seq( ETAtom( Eq( s, s ), true ) ) )

      // Structural rules
      case WeakeningLeft( subProof, ( l, formula ) ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( ETWeakening( formula, false ) +: subSequent )

      case WeakeningRight( subProof, ( l, formula ) ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( subSequent :+ ETWeakening( formula, true ) )

      case ContractionLeft( subProof, aux1, aux2 ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 ) )

      case ContractionRight( subProof, aux1, aux2 ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( subSequent.delete( aux1, aux2 ) :+ ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) )

      case c @ Cut( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val ( leftCuts, leftSequent ) = extract( leftSubProof )
        val ( rightCuts, rightSequent ) = extract( rightSubProof )
        val newCut = ETImp( leftSequent( aux1 ), rightSequent( aux2 ) )
        val cuts = if ( containsQuantifierOnLogicalLevel( c.cutFormula ) )
          newCut +: ( leftCuts ++ rightCuts )
        else leftCuts ++ rightCuts
        ( cuts, leftSequent.delete( aux1 ) ++ rightSequent.delete( aux2 ) )

      // Propositional rules
      case NegLeft( subProof, aux ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( ETNeg( subSequent( aux ) ) +: subSequent.delete( aux ) )

      case NegRight( subProof, aux ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( subSequent.delete( aux ) :+ ETNeg( subSequent( aux ) ) )

      case AndLeft( subProof, aux1, aux2 ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( ETAnd( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 ) )

      case AndRight( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val ( leftCuts, leftSequent ) = extract( leftSubProof )
        val ( rightCuts, rightSequent ) = extract( rightSubProof )
        val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
        val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
        ( leftCuts ++ rightCuts, ( leftSubSequent ++ rightSubSequent ) :+ ETAnd( leftSubTree, rightSubTree ) )

      case OrLeft( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val ( leftCuts, leftSequent ) = extract( leftSubProof )
        val ( rightCuts, rightSequent ) = extract( rightSubProof )
        val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
        val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
        ( leftCuts ++ rightCuts, ETOr( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent ) )

      case OrRight( subProof, aux1, aux2 ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        subCuts -> ( subSequent.delete( aux1, aux2 ) :+ ETOr( subSequent( aux1 ), subSequent( aux2 ) ) )

      case ImpLeft( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val ( leftCuts, leftSequent ) = extract( leftSubProof )
        val ( rightCuts, rightSequent ) = extract( rightSubProof )
        val ( leftSubTree, leftSubSequent ) = leftSequent.focus( aux1 )
        val ( rightSubTree, rightSubSequent ) = rightSequent.focus( aux2 )
        ( leftCuts ++ rightCuts, ETImp( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent ) )

      case ImpRight( subProof, aux1, aux2 ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, subSequent.delete( aux1, aux2 ) :+ ETImp( subSequent( aux1 ), subSequent( aux2 ) ) )

      // Quantifier rules
      case AllLeft( subProof, aux, _, t ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, ETWeakQuantifier( proof.mainFormulas.head._2, Map( t -> subSequent( aux ) ) ) +: subSequent.delete( aux ) )

      case AllRight( subProof, aux, main, eigen ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, subSequent.delete( aux ) :+ ETStrongQuantifier( proof.mainFormulas.head._2, eigen, subSequent( aux ) ) )

      case ExLeft( subProof, aux, main, eigen ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, ETStrongQuantifier( proof.mainFormulas.head._2, eigen, subSequent( aux ) ) +: subSequent.delete( aux ) )

      case ExRight( subProof, aux, _, t ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, subSequent.delete( aux ) :+ ETWeakQuantifier( proof.mainFormulas.head._2, Map( t -> subSequent( aux ) ) ) )

      // Skolem Quantifier rules
      case AllSkLeft( subProof, aux, _, t ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, ETWeakQuantifier( proof.mainFormulas.head._2, Map( t -> subSequent( aux ) ) ) +: subSequent.delete( aux ) )

      case r @ AllSkRight( subProof, aux, main, skolem_constant, skolem_def ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, subSequent.delete( aux ) :+ ETSkolemQuantifier( proof.mainFormulas.head._2, r.skolemTerm, skolem_def, subSequent( aux ) ) )

      case r @ ExSkLeft( subProof, aux, main, skolem_constant, skolem_def ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, ETSkolemQuantifier( proof.mainFormulas.head._2, r.skolemTerm, skolem_def, subSequent( aux ) ) +: subSequent.delete( aux ) )

      case ExSkRight( subProof, aux, _, t ) =>
        val ( subCuts, subSequent ) = extract( subProof )
        ( subCuts, subSequent.delete( aux ) :+ ETWeakQuantifier( proof.mainFormulas.head._2, Map( t -> subSequent( aux ) ) ) )

      // Equality rules
      case p @ Equality( subProof, eq, aux @ Ant( _ ), flipped, con ) =>
        val ( subCuts, sequent ) = extract( subProof )
        val ( subTree, subSequent ) = sequent.focus( aux )

        val newTree = replaceWithContext( subTree, con, p.by )
        ( subCuts, newTree +: subSequent )

      case p @ Equality( subProof, eq, aux @ Suc( _ ), flipped, con ) =>
        val ( subCuts, sequent ) = extract( subProof )
        val ( subTree, subSequent ) = sequent.focus( aux )

        val newTree = replaceWithContext( subTree, con, p.by )
        ( subCuts, subSequent :+ newTree )
    }

    r._2.antecedent.map( x => require( !x.polarity, s"Polarity of antecedent formula ${x.shallow} is positive in rule ${proof.longName}!" ) )
    r._2.succedent.map( x => require( x.polarity, s"Polarity of antecedent formula ${x.shallow} is negative in rule ${proof.longName}!" ) )
    r
  }
}
