
package gapt.proofs.ceres

import gapt.expr._
import gapt.expr.subst.PreSubstitution
import gapt.expr.util.clauseSubsumption
import gapt.expr.util.freeVariables
import gapt.expr.util.syntacticMatching
import gapt.proofs.{ HOLSequent, Sequent }

object deleteTautologies {
  def apply[T]( sequents: Seq[Sequent[T]] ): Seq[Sequent[T]] =
    sequents.filter( s => !s.antecedent.exists( f => s.succedent.contains( f ) ) )

  def apply[T]( sequents: Set[Sequent[T]] ): Set[Sequent[T]] =
    sequents.filter( s => !s.antecedent.exists( f => s.succedent.contains( f ) ) )
}

object subsumedClausesRemoval {
  def apply[T <: Formula]( sequents: List[Sequent[T]] ): List[Sequent[T]] = sequents.foldLeft( List[Sequent[T]]() )( ( ls, el ) => forward( el, backward( el, ls ) ) )
  private def forward[T <: Formula]( el: Sequent[T], ls: List[Sequent[T]] ) = if ( ls.exists( x => clauseSubsumption( x, el ).isDefined ) ) ls else ( el :: ls )
  private def backward[T <: Formula]( el: Sequent[T], ls: List[Sequent[T]] ) = ls.filterNot( x => clauseSubsumption( el, x ).isDefined )
}

// for any positive unit clause, we try to match it with all negative "ground" literals of the other clauses, if there is a match we remove the literal.
object simpleUnitResolutionNormalization {
  def apply( seqs: List[HOLSequent] ): List[HOLSequent] = {
    val posUnit = seqs.filter( x => x.antecedent.isEmpty && x.succedent.size == 1 )
    seqs.map( x => if ( !x.antecedent.isEmpty ) ( matchPos( posUnit, x ) ) else x )
  }
  private def matchPos( posUnit: List[HOLSequent], s: HOLSequent ): HOLSequent = {
    val restDomain = ( s.antecedent.flatMap( x => freeVariables( x ).toList ) ++ s.succedent.flatMap( x => freeVariables( x ).toList ) ).toSet
    val newAnt = s.antecedent.filter( x => posUnit.forall( y => syntacticMatching( List( y.succedent.head -> x ), PreSubstitution( restDomain.map { v => v -> v } ) ).isEmpty ) )
    if ( newAnt.size == s.antecedent.size ) s else new HOLSequent( newAnt, s.succedent )
  }
}

