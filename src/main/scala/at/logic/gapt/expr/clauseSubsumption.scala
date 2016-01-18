package at.logic.gapt.expr

import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.expr.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.gapt.proofs.{ Sequent, HOLSequent }

object clauseSubsumption {
  def apply( from: Sequent[LambdaExpression], to: Sequent[LambdaExpression],
             alreadyFixed:        Map[Var, LambdaExpression] = Map(),
             multisetSubsumption: Boolean                    = true ): Option[Substitution] = {
    if ( multisetSubsumption )
      if ( from.antecedent.size > to.antecedent.size || from.succedent.size > to.succedent.size )
        return None
    if ( from isEmpty ) return Some( Substitution( alreadyFixed ) )
    val chosenFrom = from.indices.head
    for (
      chosenTo <- to.indices if chosenTo sameSideAs chosenFrom;
      newSubst <- syntacticMatching( List( from( chosenFrom ) -> to( chosenTo ) ), alreadyFixed );
      subsumption <- apply(
        from delete chosenFrom,
        if ( multisetSubsumption ) to delete chosenTo else to,
        newSubst.map,
        multisetSubsumption
      )
    ) return Some( subsumption )
    None
  }
}

trait SubsumptionAlgorithm {
  /**
   * A predicate which is true iff s2 is subsumed by s1.
   * @param s1 a clause
   * @param s2 a clause
   * @return true iff s1 subsumes s2
   */
  def subsumes( s1: HOLSequent, s2: HOLSequent ): Boolean
}

object StillmanSubsumptionAlgorithmHOL extends SubsumptionAlgorithm {
  val matchAlg = NaiveIncompleteMatchingAlgorithm

  def subsumes( s1: HOLSequent, s2: HOLSequent ): Boolean = subsumes_by( s1, s2 ).nonEmpty

  /**
   * Calculates the subtitution to apply to s1 in order to subsume s2. if it exists
   * @param s1 a clause
   * @param s2 a clause
   * @return if s1 subsumes s2, the substitution necessary. None otherwise.
   */
  def subsumes_by( s1: HOLSequent, s2: HOLSequent ): Option[Substitution] = clauseSubsumption( s1, s2, multisetSubsumption = false )
}

object StillmanSubsumptionAlgorithmFOL extends SubsumptionAlgorithm {
  val matchAlg = FOLMatchingAlgorithm

  def subsumes( s1: HOLSequent, s2: HOLSequent ): Boolean = subsumes_by( s1, s2 ).nonEmpty

  def subsumes_by( s1: HOLSequent, s2: HOLSequent ): Option[FOLSubstitution] =
    clauseSubsumption( s1, s2, multisetSubsumption = false ) map { subst => FOLSubstitution( subst.map map { case ( v: FOLVar, r: FOLTerm ) => v -> r } ) }
}

