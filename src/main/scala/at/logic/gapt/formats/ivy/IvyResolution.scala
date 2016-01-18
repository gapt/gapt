package at.logic.gapt.formats.ivy

import at.logic.gapt.proofs._
import at.logic.gapt.formats.lisp.SExpression
import at.logic.gapt.expr._

/**
 * ** Implementation of Ivy's Resolution Calculus ***
 * Ivy has it's own variation of resolution which only resolves over identical literals but has an instantiation rule.
 * It should be possible to display the proofs in prooftool, but a translation to robinson resolution is neccessary for
 * many applications.
 */

sealed trait IvyResolutionProof extends SequentProof[FOLAtom, IvyResolutionProof] {
  val id: String
  val clause_exp: SExpression

  // FIXME: provide a SequentProof trait without OccConnectors
  override def mainIndices: Seq[SequentIndex] = ???
  override def occConnectors: Seq[OccConnector[FOLAtom]] = ???
  override def auxIndices: Seq[Seq[SequentIndex]] = ???
}

case class InitialClause(
    id:         String,
    clause_exp: SExpression,
    conclusion: FOLClause
) extends IvyResolutionProof {
  override def immediateSubProofs = Seq()
}

case class Instantiate(
    id:           String,
    clause_exp:   SExpression,
    substitution: FOLSubstitution,
    conclusion:   FOLClause, t: IvyResolutionProof
) extends IvyResolutionProof {
  override def immediateSubProofs = Seq( t )
}

case class Flip(
    id:         String,
    clause_exp: SExpression, flipped: SequentIndex,
    conclusion: FOLClause, t: IvyResolutionProof
) extends IvyResolutionProof {
  override def immediateSubProofs = Seq( t )
}

case class Propositional(
  id:         String,
  clause_exp: SExpression,
  conclusion: FOLClause,
  t:          IvyResolutionProof
)
    extends IvyResolutionProof {
  override def immediateSubProofs = Seq( t )
}

case class Paramodulation(
  id:              String,
  clause_exp:      SExpression,
  position:        List[Int],
  eq:              SequentIndex,
  lit:             SequentIndex,
  newLit:          FOLAtom,
  is_demodulation: Boolean, // if the formula should be left to right or right to left
  conclusion:      FOLClause,
  t1:              IvyResolutionProof,
  t2:              IvyResolutionProof
)
    extends IvyResolutionProof {
  override def immediateSubProofs = Seq( t1, t2 )
}

case class Resolution(
  id:         String,
  clause_exp: SExpression,
  lit1:       SequentIndex, //resolved literal in t1
  lit2:       SequentIndex, //resolved literal in t2
  conclusion: FOLClause,
  t1:         IvyResolutionProof,
  t2:         IvyResolutionProof
)
    extends IvyResolutionProof {
  require( t1.conclusion( lit1 ) == t2.conclusion( lit2 ) )
  require( !( lit1 sameSideAs lit2 ) )
  override def immediateSubProofs = Seq( t1, t2 )
}

case class NewSymbol(
    id:               String,
    clause_exp:       SExpression,
    lit:              SequentIndex,
    new_symbol:       FOLConst,
    replacement_term: FOLTerm,
    conclusion:       FOLClause,
    t:                IvyResolutionProof
) extends IvyResolutionProof {
  override def immediateSubProofs = Seq( t )
}
