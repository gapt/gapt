package gapt.expr

import gapt.proofs.{ Sequent, HOLSequent }

object clauseSubsumption {
  def apply(
    from:                Sequent[Expr],
    to:                  Sequent[Expr],
    alreadyFixed:        PreSubstitution   = PreSubstitution(),
    multisetSubsumption: Boolean           = false,
    matchingAlgorithm:   MatchingAlgorithm = syntacticMatching ): Option[Substitution] = {
    if ( multisetSubsumption )
      if ( from.antecedent.size > to.antecedent.size || from.succedent.size > to.succedent.size )
        return None
    if ( from isEmpty ) return Some( alreadyFixed.toSubstitution )
    val chosenFrom = from.indices.head
    println( from.antecedent.size )
    println( from( chosenFrom ) )
    println( alreadyFixed.toSubstitution )
    for {
      chosenTo <- to.indices if chosenTo sameSideAs chosenFrom
      newSubst <- matchingAlgorithm( List( from( chosenFrom ) -> to( chosenTo ) ), alreadyFixed )
      subsumption <- apply(
        from delete chosenFrom,
        if ( multisetSubsumption ) to delete chosenTo else to,
        newSubst,
        multisetSubsumption,
        matchingAlgorithm )
    } return Some( subsumption )
    println( "BLA" )
    None
  }
}
