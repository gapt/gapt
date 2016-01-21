
package at.logic.gapt.proofs.lkOld

import at.logic.gapt.proofs.{ Sequent, HOLSequent, HOLClause }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.NaiveIncompleteMatchingAlgorithm

object deleteTautologies {
  def apply[T]( sequents: Seq[Sequent[T]] ): Seq[Sequent[T]] =
    sequents.filter( s => !s.antecedent.exists( f => s.succedent.contains( f ) ) )

  def apply[T]( sequents: Set[Sequent[T]] ): Set[Sequent[T]] =
    sequents.filter( s => !s.antecedent.exists( f => s.succedent.contains( f ) ) )
}

object subsumedClausesRemovalHOL {
  val alg = StillmanSubsumptionAlgorithmHOL
  def apply[T <: HOLFormula]( sequents: List[Sequent[T]] ): List[Sequent[T]] = sequents.foldLeft( List[Sequent[T]]() )( ( ls, el ) => forward( el, backward( el, ls ) ) )
  private def forward[T <: HOLFormula]( el: Sequent[T], ls: List[Sequent[T]] ) = if ( ls.exists( x => alg.subsumes( x, el ) ) ) ls else ( el :: ls )
  private def backward[T <: HOLFormula]( el: Sequent[T], ls: List[Sequent[T]] ) = ls.filterNot( x => alg.subsumes( el, x ) )
}
object subsumedClausesRemoval {
  val alg = StillmanSubsumptionAlgorithmFOL
  def apply[T <: HOLFormula]( sequents: List[Sequent[T]] ): List[Sequent[T]] = sequents.foldLeft( List[Sequent[T]]() )( ( ls, el ) => forward( el, backward( el, ls ) ) )
  private def forward[T <: HOLFormula]( el: Sequent[T], ls: List[Sequent[T]] ) = if ( ls.exists( x => alg.subsumes( x, el ) ) ) ls else ( el :: ls )
  private def backward[T <: HOLFormula]( el: Sequent[T], ls: List[Sequent[T]] ) = ls.filterNot( x => alg.subsumes( el, x ) )
}

// for any positive unit clause, we try to match it with all negative "ground" literals of the other clauses, if there is a match we remove the literal.
object simpleUnitResolutionNormalization {
  val alg = NaiveIncompleteMatchingAlgorithm
  def apply( seqs: List[HOLSequent] ): List[HOLSequent] = {
    val posUnit = seqs.filter( x => x.antecedent.isEmpty && x.succedent.size == 1 )
    seqs.map( x => if ( !x.antecedent.isEmpty ) ( matchPos( posUnit, x ) ) else x )
  }
  private def matchPos( posUnit: List[HOLSequent], s: HOLSequent ): HOLSequent = {
    val restDomain = ( s.antecedent.flatMap( x => freeVariables( x ).toList ) ++ s.succedent.flatMap( x => freeVariables( x ).toList ) ).toSet
    val newAnt = s.antecedent.filter( x => posUnit.forall( y => alg.matchTerm( y.succedent.head, x, restDomain ) == None ) )
    if ( newAnt.size == s.antecedent.size ) s else new HOLSequent( newAnt, s.succedent )
  }
}

