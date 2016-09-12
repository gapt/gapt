package at.logic.gapt.expr

import at.logic.gapt.proofs.{ Sequent, HOLSequent }

object clauseSubsumption {
  def apply(
    from:                Sequent[LambdaExpression],
    to:                  Sequent[LambdaExpression],
    alreadyFixed:        Map[Var, LambdaExpression] = Map(),
    multisetSubsumption: Boolean                    = false,
    matchingAlgorithm:   MatchingAlgorithm          = syntacticMatching
  ): Option[Substitution] = {
    if ( multisetSubsumption )
      if ( from.antecedent.size > to.antecedent.size || from.succedent.size > to.succedent.size )
        return None
    if ( from isEmpty ) return Some( Substitution( alreadyFixed ) )
    val chosenFrom = from.indices.head
    for {
      chosenTo <- to.indices if chosenTo sameSideAs chosenFrom
      newSubst <- matchingAlgorithm( List( from( chosenFrom ) -> to( chosenTo ) ), alreadyFixed )
      subsumption <- apply(
        from delete chosenFrom,
        if ( multisetSubsumption ) to delete chosenTo else to,
        newSubst.map,
        multisetSubsumption,
        matchingAlgorithm
      )
    } return Some( subsumption )
    None
  }
}
