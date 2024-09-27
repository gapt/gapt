package gapt.logic

import gapt.expr.Expr
import gapt.expr.formula.Eq
import gapt.expr.subst.PreSubstitution
import gapt.expr.subst.Substitution
import gapt.expr.util.syntacticMatching
import gapt.proofs.Sequent

object clauseSubsumption {
  def apply(
    from:                Sequent[Expr],
    to:                  Sequent[Expr],
    alreadyFixed:        PreSubstitution = PreSubstitution(),
    multisetSubsumption: Boolean         = false ): Option[Substitution] = {
    if ( multisetSubsumption )
      if ( from.antecedent.size > to.antecedent.size || from.succedent.size > to.succedent.size )
        return None
    if ( from isEmpty ) return Some( alreadyFixed.toSubstitution )
    val chosenFrom = from.indices.head
    for {
      chosenTo <- to.indices if chosenTo sameSideAs chosenFrom
      newSubst <- syntacticMatching( from( chosenFrom ), to( chosenTo ), alreadyFixed )
      subsumption <- apply(
        from delete chosenFrom,
        if ( multisetSubsumption ) to delete chosenTo else to,
        newSubst,
        multisetSubsumption )
    } return Some( subsumption )
    None
  }

  private def eqVariants( e: Expr ): Seq[Expr] =
    e match {
      case Eq( l, r ) => Seq( e, Eq( r, l ) )
      case _          => Seq( e )
    }
  def modEqSymm(
    from:                Sequent[Expr],
    to:                  Sequent[Expr],
    alreadyFixed:        PreSubstitution = PreSubstitution(),
    multisetSubsumption: Boolean         = false ): Option[Substitution] = {
    if ( multisetSubsumption )
      if ( from.antecedent.size > to.antecedent.size || from.succedent.size > to.succedent.size )
        return None
    if ( from isEmpty ) return Some( alreadyFixed.toSubstitution )
    val chosenFrom = from.indices.head
    for {
      chosenTo <- to.indices if chosenTo sameSideAs chosenFrom
      toE <- eqVariants( to( chosenTo ) )
      newSubst <- syntacticMatching( from( chosenFrom ), toE, alreadyFixed )
      subsumption <- modEqSymm(
        from delete chosenFrom,
        if ( multisetSubsumption ) to delete chosenTo else to,
        newSubst,
        multisetSubsumption )
    } return Some( subsumption )
    None
  }
}
