package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.lkskNew.LKskProof.Label
import at.logic.gapt.proofs.{ Suc, Ant, Sequent }
import at.logic.gapt.proofs.ceres.{ Struct, A, Dual, Times, Plus, StructCreators }
import at.logic.gapt.proofs.lkskNew._

object extractStructFromLKsk {
  /* lksk passes labels on */

  def apply( p: LKskProof ): Struct[Label] =
    apply( p, _ => true )

  def apply( p: LKskProof, cutFormulaPred: HOLFormula => Boolean ): Struct[Label] =
    apply( p, p.conclusion map { _ => false }, cutFormulaPred )

  def apply( p: LKskProof, isCutAncestor: Sequent[Boolean], cutFormulaPred: HOLFormula => Boolean ): Struct[Label] = p match {
    case Axiom( antLabel, sucLabel, atom ) =>
      val ant = if ( isCutAncestor( Ant( 0 ) ) )
        Dual( A( atom, antLabel :: Nil ) ) :: Nil
      else
        Nil
      val suc = if ( isCutAncestor( Suc( 0 ) ) )
        A( atom, List( antLabel ) ) :: Nil
      else
        Nil
      Times( ant ::: suc, Nil )
    case p @ Cut( subProof1, aux1, subProof2, aux2 ) if cutFormulaPred( p.cutFormula ) =>
      Plus(
        apply( p.subProof1, p.occConnectors( 0 ).parents( isCutAncestor ).map( _.headOption getOrElse true ), cutFormulaPred ),
        apply( p.subProof2, p.occConnectors( 1 ).parents( isCutAncestor ).map( _.headOption getOrElse true ), cutFormulaPred )
      )
    case p @ Cut( subProof1, aux1, subProof2, aux2 ) if !cutFormulaPred( p.cutFormula ) =>
      Times(
        apply( p.subProof1, p.occConnectors( 0 ).parents( isCutAncestor ).map( _.headOption getOrElse false ), cutFormulaPred ),
        apply( p.subProof2, p.occConnectors( 1 ).parents( isCutAncestor ).map( _.headOption getOrElse false ), cutFormulaPred ),
        Nil
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
        Nil
      )
  }

}
