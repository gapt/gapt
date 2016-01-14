package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr.{ Eq, HOLFormula }
import at.logic.gapt.proofs.lkskNew.LKskProof.Label
import at.logic.gapt.proofs.{ Suc, Ant, Sequent }
import at.logic.gapt.proofs.ceres._
import at.logic.gapt.proofs.lkskNew._

object extractStructFromLKsk {
  /* lksk passes labels on */

  def apply( p: LKskProof ): Struct[Label] =
    apply( p, _ => true )

  def apply( p: LKskProof, cutFormulaPred: HOLFormula => Boolean ): Struct[Label] =
    apply( p, p.conclusion map { _ => false }, cutFormulaPred )

  def apply( p: LKskProof, isCutAncestor: Sequent[Boolean], cutFormulaPred: HOLFormula => Boolean ): Struct[Label] = p match {
    //TODO: I think the labels are always empty, because cut-ancestors never lead into skolem quantifier rules. perhaps check.
    case Axiom( antLabel, sucLabel, atom ) =>
      ( isCutAncestor( Ant( 0 ) ), isCutAncestor( Suc( 0 ) ) ) match {
        case ( true, true ) =>
          EmptyPlusJunction()
        case ( true, false ) =>
          //println( s"negative: $atom" )
          Dual( A( atom, List( antLabel ) ) )
        case ( false, true ) =>
          //println( s"positive: $atom" )
          A( atom, List( antLabel ) )
        case ( false, false ) =>
          EmptyTimesJunction()
      }
    case p @ Reflexivity( antLabel, term ) =>
      if ( isCutAncestor( Suc( 0 ) ) )
        A( Eq( term, term ), List( antLabel ) )
      else
        EmptyTimesJunction()
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
    case Equality( upperProof, eq, aux, flipped, pos ) =>
      val new_occs = p.occConnectors.head.parents( isCutAncestor ).map( _ head )

      val struct = apply( upperProof, new_occs, cutFormulaPred )
      val e_idx_conclusion = p.occConnectors( 0 ).child( eq )
      //println( "eql: " + p.endSequent( eq ) )
      ( isCutAncestor( p.mainIndices( 0 ) ), isCutAncestor( e_idx_conclusion ) ) match {
        case ( true, true ) =>
          struct
        case ( true, false ) =>
          val eqf = p.conclusion( e_idx_conclusion )
          Plus[Label]( A( eqf._2, List( eqf._1 ) ), struct )
        case ( false, true ) =>
          val eqf = p.conclusion( e_idx_conclusion )
          Times( Dual( A( eqf._2, List( eqf._1 ) ) ), struct, List( eqf._1 ) )
        case ( false, false ) =>
          struct
      }
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
