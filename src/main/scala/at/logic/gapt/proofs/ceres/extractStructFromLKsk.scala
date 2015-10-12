package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.{ Suc, Ant, Sequent }
import at.logic.gapt.proofs.ceres.struct._
import at.logic.gapt.proofs.lksk.LabelledFormulaOccurrence
import at.logic.gapt.proofs.lkskNew._

object extractStructFromLKsk {
  def apply( p: LKskProof ): Struct =
    apply( p, _ => true )

  def apply( p: LKskProof, cutFormulaPred: HOLFormula => Boolean ): Struct =
    apply( p, p.conclusion map { _ => false }, cutFormulaPred )

  def apply( p: LKskProof, isCutAncestor: Sequent[Boolean], cutFormulaPred: HOLFormula => Boolean ): Struct = p match {
    case Axiom( antLabel, sucLabel, atom ) =>
      // TODO: this is identical to the initial sequent case, except that the labels are swapped?????
      val ant = if ( isCutAncestor( Ant( 0 ) ) )
        Dual( A( new LabelledFormulaOccurrence( atom, Nil, sucLabel.toSet ).asInstanceOf[FormulaOccurrence] ) ) :: Nil
      else
        Nil
      val suc = if ( isCutAncestor( Suc( 0 ) ) )
        A( new LabelledFormulaOccurrence( atom, Nil, antLabel.toSet ).asInstanceOf[FormulaOccurrence] ) :: Nil
      else
        Nil
      StructCreators.makeTimesJunction( ant ::: suc, Nil )
    case p: InitialSequent =>
      val cutAncestors = p.conclusion zip isCutAncestor filter { _ _2 } map { _ _1 }
      StructCreators.makeTimesJunction(
        cutAncestors.
        map { case ( l, f ) => new LabelledFormulaOccurrence( f, Nil, l.toSet ).asInstanceOf[FormulaOccurrence] }.
        map( a => Dual( A( a ) ), s => A( s ) ).
        elements.toList, Nil
      )
    case p @ Cut( subProof1, aux1, subProof2, aux2 ) if cutFormulaPred( p.cutFormula ) =>
      Plus(
        apply( p.subProof1, p.occConnectors( 0 ).parents( isCutAncestor ).map( _.headOption getOrElse true ), cutFormulaPred ),
        apply( p.subProof2, p.occConnectors( 1 ).parents( isCutAncestor ).map( _.headOption getOrElse true ), cutFormulaPred )
      )
    case p @ Cut( subProof1, aux1, subProof2, aux2 ) if !cutFormulaPred( p.cutFormula ) =>
      Times(
        apply( p.subProof1, p.occConnectors( 0 ).parents( isCutAncestor ).map( _.headOption getOrElse false ), cutFormulaPred ),
        apply( p.subProof2, p.occConnectors( 1 ).parents( isCutAncestor ).map( _.headOption getOrElse false ), cutFormulaPred )
      )
    case p: UnaryRule =>
      apply( p.subProof, p.occConnectors.head.parents( isCutAncestor ).map( _ head ), cutFormulaPred )
    case p: BinaryRule if isCutAncestor( p.mainIndices.head ) =>
      Plus(
        apply( p.subProof1, p.occConnectors( 0 ).parents( isCutAncestor ).map( _ head ), cutFormulaPred ),
        apply( p.subProof2, p.occConnectors( 1 ).parents( isCutAncestor ).map( _ head ), cutFormulaPred )
      )
    case p: BinaryRule if !isCutAncestor( p.mainIndices.head ) =>
      Times(
        apply( p.subProof1, p.occConnectors( 0 ).parents( isCutAncestor ).map( _ head ), cutFormulaPred ),
        apply( p.subProof2, p.occConnectors( 1 ).parents( isCutAncestor ).map( _ head ), cutFormulaPred ),
        Nil /* TODO: why should I pass the list of cut-ancestors here? */ )
  }

}
