package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion._

/**
 * Extends expansion tree extraction to lksk.
 */
object LKskToExpansionProof {
  /*
  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   * Dp(Ex(π)) might not be tautological, e.g. if π contains quantified cuts.
   * The induction rule is not supported!
   *
   * @param proof The proof π.
   * @return The expansion proof Ex(π).
   */
  def apply( proof: LKskProof ): ExpansionSequent =
    merge( extract( proof ) )

  private def extract( proof: LKskProof ): Sequent[ExpansionTreeWithMerges] = proof match {

    // Axioms
    case Axiom( _, _, atom: HOLAtom )               => Sequent( Seq( ETAtom( atom ) ), Seq( ETAtom( atom ) ) )

    case Reflexivity( _, s )                        => Sequent( Seq(), Seq( ETAtom( Eq( s, s ) ) ) )

    case TopRight( _ )                              => Sequent( Seq(), Seq( ETTop ) )

    case BottomLeft( _ )                            => Sequent( Seq( ETBottom ), Seq() )

    // Structural rules
    case WeakeningLeft( subProof, ( _, formula ) )  => ETWeakening( formula ) +: extract( subProof )

    case WeakeningRight( subProof, ( _, formula ) ) => extract( subProof ) :+ ETWeakening( formula )

    case ContractionLeft( subProof, aux1, aux2 ) =>
      val subSequent = extract( subProof )
      ETMerge( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 )

    case ContractionRight( subProof, aux1, aux2 ) =>
      val subSequent = extract( subProof )
      subSequent.delete( aux1, aux2 ) :+ ETMerge( subSequent( aux1 ), subSequent( aux2 ) )

    case Cut( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val leftSubSequent = extract( leftSubProof ).delete( aux1 )
      val rightSubSequent = extract( rightSubProof ).delete( aux2 )
      leftSubSequent ++ rightSubSequent

    // Propositional rules
    case NegLeft( subProof, aux ) =>
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      ETNeg( subTree ) +: subSequent

    case NegRight( subProof, aux ) =>
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      subSequent :+ ETNeg( subTree )

    case AndLeft( subProof, aux1, aux2 ) =>
      val subSequent = extract( subProof )
      ETAnd( subSequent( aux1 ), subSequent( aux2 ) ) +: subSequent.delete( aux1, aux2 )

    case AndRight( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubTree, leftSubSequent ) = extract( leftSubProof ).focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = extract( rightSubProof ).focus( aux2 )
      ( leftSubSequent ++ rightSubSequent ) :+ ETAnd( leftSubTree, rightSubTree )

    case OrLeft( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubTree, leftSubSequent ) = extract( leftSubProof ).focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = extract( rightSubProof ).focus( aux2 )
      ETOr( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent )

    case OrRight( subProof, aux1, aux2 ) =>
      val subSequent = extract( subProof )
      subSequent.delete( aux1, aux2 ) :+ ETOr( subSequent( aux1 ), subSequent( aux2 ) )

    case ImpLeft( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubTree, leftSubSequent ) = extract( leftSubProof ).focus( aux1 )
      val ( rightSubTree, rightSubSequent ) = extract( rightSubProof ).focus( aux2 )
      ETImp( leftSubTree, rightSubTree ) +: ( leftSubSequent ++ rightSubSequent )

    case ImpRight( subProof, aux1, aux2 ) =>
      val subSequent = extract( subProof )
      subSequent.delete( aux1, aux2 ) :+ ETImp( subSequent( aux1 ), subSequent( aux2 ) )

    // Quantifier rules
    case AllSkLeft( subProof, aux, _, t ) =>
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      ETWeakQuantifier( proof.mainFormulas.head._2, Seq( subTree -> t ) ) +: subSequent

    case AllSkRight( subProof, aux, main, skolemconst ) =>
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      subSequent :+ ETSkolemQuantifier( proof.mainFormulas.head._2, skolemconst, subTree )

    case ExSkLeft( subProof, aux, main, skolemconst ) =>
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      ETSkolemQuantifier( proof.mainFormulas.head._2, skolemconst, subTree ) +: subSequent

    case ExSkRight( subProof, aux, _, t ) =>
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      subSequent :+ ETWeakQuantifier( proof.mainFormulas.head._2, Seq( subTree -> t ) )

    // Equality rules
    case Equality( subProof, eq, aux, flipped, pos ) =>
      println( s"converting equality on ${subProof.conclusion( eq )._2} and ${subProof.conclusion( aux )._2}" )
      val ( subTree, subSequent ) = extract( subProof ).focus( aux )
      val main = subProof.conclusion( aux )._2
      val repTerm = main( pos.head )
      val holpos = pos map ( HOLPosition.toHOLPosition( main ) )
      val newTree = holpos.foldLeft( subTree ) { ( acc, p ) => replaceAtHOLPosition( acc, p, repTerm ) }
      newTree +: subSequent

  }
  */
}
