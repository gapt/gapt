package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base._

abstract class LKProof {
  /**
   * The name of the rule.
   *
   * @return
   */
  def name: String

  /**
   * A list of SequentIndices denoting the main formula(s) of the rule.
   *
   * @return
   */
  def mainIndices: Seq[SequentIndex]

  /**
   * The list of main formulas of the rule.
   *
   * @return
   */
  def mainFormulas: Seq[HOLFormula] = mainIndices map { endSequent( _ ) }

  /**
   * A list of lists of SequentIndices denoting the auxiliary formula(s) of the rule.
   * The first list contains the auxiliary formulas in the first premise and so on.
   *
   * @return
   */
  def auxIndices: Seq[Seq[SequentIndex]]

  /**
   * The end-sequent of the rule.
   *
   * @return
   */
  def endSequent: HOLSequent

  /**
   * The immediate subproofs of the rule.
   *
   * @return
   */
  def subProofs: Seq[LKProof]

  /**
   * The upper sequents of the rule.
   *
   * @return
   */
  def premises: Seq[HOLSequent] = subProofs map ( _.endSequent )

  /**
   * A list of lists containing the auxiliary formulas of the rule.
   * The first list constains the auxiliary formulas in the first premise and so on.
   *
   * @return
   */
  def auxFormulas: Seq[Seq[HOLFormula]] = for ( ( p, is ) <- premises zip auxIndices ) yield p( is )

  /**
   * Returns the subproofs of this in post order.
   *
   * @return
   */
  def postOrder: Seq[LKProof]
}

/**
 * An LKProof deriving a sequent from another sequent:
 *
 *        (π)
 *      Γ :- Δ
 *    ----------
 *     Γ' :- Δ'
 *
 */
abstract class UnaryLKProof extends LKProof {
  /**
   * The immediate subproof of the rule.
   *
   * @return
   */
  def subProof: LKProof

  /**
   * The object connecting the lower and upper sequents.
   *
   * @return
   */
  def getOccConnector: OccConnector

  /**
   * The upper sequent of the rule.
   *
   * @return
   */
  def premise = subProof.endSequent

  override def subProofs = Seq( subProof )

  override def postOrder = subProof.postOrder :+ this
}

object UnaryLKProof {
  def unapply( p: UnaryLKProof ) = Some( p.endSequent, p.subProof )
}

/**
 * An LKProof deriving a sequent from two other sequents:
 *
 *     (π1)     (π2)
 *    Γ :- Δ   Γ' :- Δ'
 *   ------------------
 *        Π :- Λ
 *
 */
abstract class BinaryLKProof extends LKProof {
  /**
   * The immediate left subproof of the rule.
   *
   * @return
   */
  def leftSubProof: LKProof

  /**
   * The immediate right subproof of the rule.
   *
   * @return
   */
  def rightSubProof: LKProof

  /**
   * The object connecting the lower and left upper sequents.
   *
   * @return
   */
  def getLeftOccConnector: OccConnector

  /**
   * The object connecting the lower and right upper sequents.
   *
   * @return
   */
  def getRightOccConnector: OccConnector

  /**
   * The left upper sequent of the rule.
   *
   * @return
   */
  def leftPremise = leftSubProof.endSequent

  /**
   * The right upper sequent of the rule.
   *
   * @return
   */
  def rightPremise = rightSubProof.endSequent

  override def subProofs = Seq( leftSubProof, rightSubProof )

  override def postOrder = leftSubProof.postOrder ++ rightSubProof.postOrder :+ this
}

object BinaryLKProof {
  def unapply( p: BinaryLKProof ) = Some( p.endSequent, p.leftSubProof, p.rightSubProof )
}

// <editor-fold desc="Axioms">

/**
 * An LKProof consisting of a single sequent:
 *
 *     --------ax
 *      Γ :- Δ
 *
 */
abstract class InitialSequent extends LKProof {

  override def name = "ax"

  override def mainIndices = endSequent.indices

  override def auxIndices = Seq()

  override def subProofs = Seq()

  override def postOrder = Seq( this )
}

object InitialSequent {
  def unapply( proof: InitialSequent ) = Some( proof.endSequent )
}

case class ArbitraryAxiom( endSequent: HOLSequent ) extends InitialSequent {

}

/**
 * An LKProof introducing ⊤ on the right:
 *
 *       --------⊤:r
 *         :- ⊤
 */
case object TopAxiom extends InitialSequent { override def name: String = "⊤:r"; override def endSequent = HOLSequent( Nil, Seq( Top() ) ); def mainFormula = Top() }

/**
 * An LKProof introducing ⊥ on the left:
 *
 *       --------⊥:l
 *         ⊥ :-
 */
case object BottomAxiom extends InitialSequent { override def name: String = "⊥:l"; override def endSequent = HOLSequent( Seq( Bottom() ), Nil ); def mainFormula = Top() }

/**
 * An LKProof consisting of a logical axiom:
 *
 *    --------ax
 *     A :- A
 *
 * with A atomic.
 *
 * @param A The atom A.
 */
case class LogicalAxiom( A: HOLAtom ) extends InitialSequent { override def endSequent = HOLSequent( Seq( A ), Seq( A ) ); def mainFormula = A }

/**
 * An LKProof consisting of a reflexivity axiom:
 *
 *    ------------ax
 *      :- s = s
 *
 * with s a term.
 *
 * @param s The term s.
 */
case class ReflexivityAxiom( s: LambdaExpression ) extends InitialSequent { override def endSequent = HOLSequent( Seq(), Seq( Eq( s, s ) ) ); def mainFormula = Eq( s, s ) }

// </editor-fold>

// <editor-fold desc="Structural rules">

/**
 * An LKProof ending with a left contraction:
 *
 *         (π)
 *     A, A, Γ :- Δ
 *    --------------
 *      A, Γ :- Δ
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof {

  // <editor-fold desc="Sanity checks">

  ( aux1, aux2 ) match {
    case ( Ant( _ ), Ant( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: One of $aux1 and $aux2 is in the succedent." )
  }

  if ( aux1 == aux2 )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Indices of aux formulas are equal." )

  if ( !( premise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Sequent $premise is not defined at index $aux1." )

  if ( !( premise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Sequent $premise is not defined at index $aux2." )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Auxiliar formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )
  // </editor-fold>

  val mainFormula = premise( aux1 )
  val ( a1, a2 ) = if ( aux1 <= aux2 ) ( aux1, aux2 ) else ( aux2, aux1 )

  private val newContext = premise delete a2 delete a1

  // <editor-fold desc="Overrides">

  override def endSequent = mainFormula +: newContext

  override def mainIndices = Seq( Ant( 0 ) )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "c:l"

  override def getOccConnector = new OccConnector(
    endSequent,
    premise,
    Seq( aux1, aux2 ) +: ( premise.indicesSequent delete a2 delete a1 map { i => Seq( i ) } )
  )

  // </editor-fold>
}

object ContractionLeftRule {
  /**
   * Convenience constructor for c:l that, given a formula to contract on the left, will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: HOLFormula ): ContractionLeftRule = {
    val premise = subProof.endSequent
    val i = premise.antecedent indexOf f
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Aux formula $f not found in antecedent of $premise." )

    val j = premise.antecedent indexOf ( f, i + 1 )

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Aux formula $f only found once in antecedent of $premise." )

    new ContractionLeftRule( subProof, Ant( i ), Ant( j ) )
  }

}

/**
 * An LKProof ending with a right contraction:
 *
 *         (π)
 *     Γ :- Δ, A, A
 *    --------------
 *      Γ :- Δ, A
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof {

  // <editor-fold desc="Sanity checks">

  ( aux1, aux2 ) match {
    case ( Suc( _ ), Suc( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create ContractionRightRule: One of $aux1 and $aux2 is in the antecedent." )
  }

  if ( aux1 == aux2 )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Indices of aux formulas are equal." )

  if ( !( premise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Sequent $premise is not defined at index $aux1." )

  if ( !( premise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Sequent $premise is not defined at index $aux2." )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Auxiliar formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )
  // </editor-fold>

  val mainFormula = premise( aux1 )
  val ( a1, a2 ) = if ( aux1 <= aux2 ) ( aux1, aux2 ) else ( aux2, aux1 )

  private val newContext = premise.delete( a2 ).delete( a1 )

  // <editor-fold desc="Overrides">

  override def endSequent = newContext :+ mainFormula

  private val n = endSequent.succedent.length - 1

  override def mainIndices = Seq( Suc( n ) )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "c:r"

  override def getOccConnector = new OccConnector(
    endSequent,
    premise,
    ( premise.indicesSequent delete a2 delete a1 map { i => Seq( i ) } ) :+ Seq( aux1, aux2 )
  )

  // </editor-fold>
}

object ContractionRightRule {
  /**
   * Convenience constructor for c:r that, given a formula to contract on the right, will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: HOLFormula ): ContractionRightRule = {
    val premise = subProof.endSequent
    val i = premise.succedent indexOf f
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Aux formula $f not found in succedent of $premise." )

    val j = premise.succedent indexOf ( f, i + 1 )

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Aux formula $f only found once in succedent of $premise." )

    new ContractionRightRule( subProof, Suc( i ), Suc( j ) )
  }

}

/**
 * An LKProof ending with a left weakening:
 *
 *        (π)
 *       Γ :- Δ
 *     ---------w:l
 *     A, Γ :- Δ
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningLeftRule( subProof: LKProof, formula: HOLFormula ) extends UnaryLKProof {
  def endSequent = formula +: premise
  def auxIndices = Seq( Seq() )
  def name = "w:l"
  def mainIndices = Seq( Ant( 0 ) )
  def mainFormula = formula

  def getOccConnector = new OccConnector(
    endSequent,
    premise,
    Seq() +: ( premise.indicesSequent map { i => Seq( i ) } )
  )
}

/**
 * An LKProof ending with a right weakening:
 *
 *        (π)
 *       Γ :- Δ
 *     ---------w:r
 *     Γ :- Δ, A
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningRightRule( subProof: LKProof, formula: HOLFormula ) extends UnaryLKProof {
  def endSequent = premise :+ formula
  def auxIndices = Seq( Seq() )
  def name = "w:r"

  private val n = endSequent.succedent.length - 1
  def mainIndices = Seq( Suc( n ) )
  def mainFormula = formula

  def getOccConnector = new OccConnector(
    endSequent,
    premise,
    ( premise.indicesSequent map { i => Seq( i ) } ) :+ Seq()
  )
}

/**
 * An LKProof ending with a cut:
 *
 *      (π1)         (π2)
 *    Γ :- Δ, A   A, Π :- Λ
 *   ------------------------
 *        Γ, Π :- Δ, Λ
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A in π,,1,,.
 * @param rightSubProof The proof π,,2,,.
 * @param aux2 The index of A in π,,2,,.
 */
case class CutRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof {
  // <editor-fold desc="Sanity checks">
  ( aux1, aux2 ) match {
    case ( Suc( _ ), Ant( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create CutRule: One of $aux1 and $aux2 is in the wrong cedent." )
  }

  if ( !( leftPremise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create AndRightRule: Sequent $leftPremise is not defined at index $aux1." )

  if ( !( rightPremise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create AndRightRule: Sequent $leftPremise is not defined at index $aux2." )

  if ( leftPremise( aux1 ) != rightPremise( aux2 ) )
    throw new LKRuleCreationException( s"Cannot create CutRule: Auxiliar formulas are not the same." )
  // </editor-fold>

  private val ( leftContext, rightContext ) = ( leftPremise delete aux1, rightPremise delete aux2 )
  def endSequent = leftContext ++ rightContext

  def name = "cut"

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  def mainIndices = Seq()

  def getLeftOccConnector = new OccConnector(
    endSequent,
    leftPremise,
    ( leftPremise.indicesSequent delete aux1 map { i => Seq( i ) } ) ++ ( rightPremise delete aux2 map { i => Seq() } )
  )

  def getRightOccConnector = new OccConnector(
    endSequent,
    rightPremise,
    ( leftPremise delete aux1 map { i => Seq() } ) ++ ( rightPremise.indicesSequent delete aux2 map { i => Seq( i ) } )

  )
}

object CutRule {
  /**
   * Convenience constructor for cut that, given a formula A, will attempt to create a cut inference with that cut formula.
   *
   * @param leftSubProof
   * @param rightSubProof
   * @param A
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, A: HOLFormula ): CutRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )
    val i = leftPremise.succedent indexOf A
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create CutRule: Aux formula $A not found in succedent of $leftPremise." )

    val j = rightPremise.antecedent indexOf A

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create CutRule: Aux formula $A not found in antecedent of $rightPremise." )

    new CutRule( leftSubProof, Suc( i ), rightSubProof, Ant( j ) )
  }
}

// </editor-fold>

// <editor-fold desc="Propositional rules>

/**
 * An LKProof ending with a negation on the left:
 *
 *       (π)
 *    Γ :- Δ, A
 *   -----------¬:l
 *   ¬A, Γ :- Δ
 *
 * @param subProof The proof π.
 * @param aux The index of A in the succedent.
 */
case class NegLeftRule( subProof: LKProof, aux: SequentIndex ) extends UnaryLKProof {

  // <editor-fold desc="Sanity checks">
  aux match {
    case Ant( _ ) => throw new LKRuleCreationException( s"Cannot create NegLeftRule: $aux is in the antecedent." )
    case Suc( _ ) =>
  }

  if ( !premise.isDefinedAt( aux ) )
    throw new LKRuleCreationException( s"Cannot create NegLeftRule: Sequent $premise is not defined at index $aux." )

  // </editor-fold>

  val ( auxFormula, context ) = premise.focus( aux )
  val mainFormula = Neg( auxFormula )

  override def auxIndices = Seq( Seq( aux ) )
  override def mainIndices = Seq( Ant( 0 ) )
  override def endSequent = mainFormula +: context
  override def name = "¬:l"

  override def getOccConnector = new OccConnector(
    endSequent,
    premise,
    Seq( aux ) +: ( premise.indicesSequent delete aux map { i => Seq( i ) } )
  )
}

object NegLeftRule {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof
   * @param formula
   * @return
   */
  def apply( subProof: LKProof, formula: HOLFormula ): NegLeftRule = {
    val premise = subProof.endSequent

    val i = premise.succedent indexOf formula

    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create NegLeftRule: $formula not found in succedent of $premise." )

    new NegLeftRule( subProof, Suc( i ) )
  }
}

/**
 * An LKProof ending with a negation on the right:
 *
 *       (π)
 *    A, Γ :- Δ
 *   -----------¬:r
 *   Γ :- Δ, ¬A
 *
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 */
case class NegRightRule( subProof: LKProof, aux: SequentIndex ) extends UnaryLKProof {

  // <editor-fold desc="Sanity checks">
  aux match {
    case Ant( _ ) =>
    case Suc( _ ) => throw new LKRuleCreationException( s"Cannot create NegRightRule: $aux is in the succedent." )
  }

  if ( !premise.isDefinedAt( aux ) )
    throw new LKRuleCreationException( s"Cannot create NegRightRule: Sequent $premise is not defined at index $aux." )

  // </editor-fold>

  val ( auxFormula, context ) = premise.focus( aux )
  val mainFormula = Neg( auxFormula )

  private val n = endSequent.length - 1
  override def auxIndices = Seq( Seq( aux ) )
  override def mainIndices = Seq( Suc( n ) )
  override def endSequent = context :+ mainFormula
  override def name = "¬:r"

  override def getOccConnector = new OccConnector(
    endSequent,
    premise,
    ( premise.indicesSequent delete aux map { i => Seq( i ) } ) :+ Seq( aux )
  )
}

object NegRightRule {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof
   * @param formula
   * @return
   */
  def apply( subProof: LKProof, formula: HOLFormula ): NegRightRule = {
    val premise = subProof.endSequent

    val i = premise.antecedent indexOf formula

    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create NegRightRule: $formula not found in antecedent of $premise." )

    new NegRightRule( subProof, Ant( i ) )
  }
}

/**
 * An LKProof ending with a conjunction on the left:
 *
 *         (π)
 *     A, B, Γ :- Δ
 *    --------------
 *    A ∧ B, Γ :- Δ
 *
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class AndLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof {

  // <editor-fold desc="Sanity checks">

  ( aux1, aux2 ) match {
    case ( Ant( _ ), Ant( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: One of $aux1 and $aux2 is in the succedent." )
  }

  if ( aux1 == aux2 )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Indices of aux formulas are equal." )

  if ( !( premise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Sequent $premise is not defined at index $aux1." )

  if ( !( premise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionLeftRule: Sequent $premise is not defined at index $aux2." )
  // </editor-fold>

  val leftConjunct = premise( aux1 )
  val rightConjunct = premise( aux2 )
  val formula = And( leftConjunct, rightConjunct )
  val ( a1, a2 ) = if ( aux1 <= aux2 ) ( aux1, aux2 ) else ( aux2, aux1 )

  val newContext = premise delete a2 delete a1

  // <editor-fold desc="Overrides">

  override def endSequent = formula +: newContext

  override def mainIndices = Seq( Ant( 0 ) )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∧:l"

  override def getOccConnector = new OccConnector(
    endSequent,
    premise,
    Seq( aux1, aux2 ) +: ( premise.indicesSequent delete a2 delete a1 map { i => Seq( i ) } )
  )

  // </editor-fold>
}

object AndLeftRule {
  /**
   * Convenience constructor for ∧:l that, given two formulas on the left, will automatically pick the respective first instances of these formulas.
   *
   * @param subProof
   * @param A
   * @param B
   * @return
   */
  def apply( subProof: LKProof, A: HOLFormula, B: HOLFormula ): AndLeftRule = {
    val premise = subProof.endSequent
    val i = premise.antecedent indexOf A
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create AndLeftRule: Aux formula $A not found in antecedent of $premise." )

    val j =
      if ( A == B )
        premise.antecedent indexOf ( B, i + 1 )
      else
        premise.antecedent indexOf B

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create AndLeftRule: Aux formula $B not found in antecedent of $premise." )

    new AndLeftRule( subProof, Ant( i ), Ant( j ) )
  }

  /**
   * Convenience constructor for ∧:l that, given a proposed main formula A ∧ B, will attempt to create an inference with this main formula.
   *
   * @param subProof
   * @param F
   * @return
   */
  def apply( subProof: LKProof, F: HOLFormula ): AndLeftRule = F match {
    case And( f, g ) => apply( subProof, f, g )
    case _           => throw new LKRuleCreationException( s"Cannot create AndLeftRule: Proposed main formula $F is not a conjunction." )
  }
}

/**
 * An LKProof ending with a conjunction on the right:
 *
 *    (π1)         (π2)
 *   Γ :- Δ, A    Π :- Λ, B
 * --------------------------
 *     Γ, Π :- Δ, Λ, A∧B
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class AndRightRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof {

  // <editor-fold desc="Sanity checks">
  ( aux1, aux2 ) match {
    case ( Suc( _ ), Suc( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create AndRightRule: One of $aux1 and $aux2 is in the antecedent." )
  }

  if ( !( leftPremise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create AndRightRule: Sequent $leftPremise is not defined at index $aux1." )

  if ( !( rightPremise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create AndRightRule: Sequent $leftPremise is not defined at index $aux2." )

  // </editor-fold>

  val ( leftConjunct, leftContext ) = leftPremise focus aux1
  val ( rightConjunct, rightContext ) = rightPremise focus aux2

  val formula = And( leftConjunct, rightConjunct )

  def endSequent = leftContext ++ rightContext :+ formula

  private val n = endSequent.sizes._2 - 1

  def mainIndices = Seq( Suc( n ) )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  def name = "∧:r"

  def getLeftOccConnector = new OccConnector(
    endSequent,
    leftPremise,
    ( leftPremise.indicesSequent delete aux1 map { Seq.apply( _ ) } ) ++ ( rightPremise delete aux2 map { i => Seq() } ) :+ Seq( aux1 )
  )

  def getRightOccConnector = new OccConnector(
    endSequent,
    rightPremise,
    ( leftPremise delete aux1 map { i => Seq() } ) ++ ( rightPremise.indicesSequent delete aux2 map { Seq.apply( _ ) } ) :+ Seq( aux2 )
  )

}

object AndRightRule {
  /**
   * Convenience constructor for ∧:r that, given formulas on the right, will automatically pick their respective first occurrences.
   *
   * @param leftSubProof
   * @param A
   * @param rightSubProof
   * @param B
   * @return
   */
  def apply( leftSubProof: LKProof, A: HOLFormula, rightSubProof: LKProof, B: HOLFormula ): AndRightRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val i = leftPremise.succedent indexOf A
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create AndRightRule: Aux formula $A not found in succedent of $leftPremise." )

    val j = rightPremise.succedent indexOf B

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create AndRightRule: Aux formula $B not found in antecedent of $rightPremise." )

    new AndRightRule( leftSubProof, Suc( i ), rightSubProof, Suc( j ) )
  }

  /**
   * Convenience constructor for ∧:r that, given a proposed main formula A ∧ B, will attempt to create an inference with this main formula.
   *
   * @param leftSubProof
   * @param rightSubProof
   * @param F
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, F: HOLFormula ): AndRightRule = F match {
    case And( f, g ) => apply( leftSubProof, f, rightSubProof, g )
    case _           => throw new LKRuleCreationException( s"Cannot create AndRightRule: Proposed main formula $F is not a conjunction." )
  }
}

/**
 * An LKProof ending with a disjunction on the left:
 *
 *     (π1)         (π2)
 *   A, Γ :- Δ    B, Π :- Λ
 * --------------------------
 *     A∨B, Γ, Π :- Δ, Λ
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class OrLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof {

  // <editor-fold desc="Sanity checks">
  ( aux1, aux2 ) match {
    case ( Ant( _ ), Ant( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create OrLeftRule: One of $aux1 and $aux2 is in the succedent." )
  }

  if ( !( leftPremise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create OrLeftRule: Sequent $leftPremise is not defined at index $aux1." )

  if ( !( rightPremise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create OrLeftRule: Sequent $leftPremise is not defined at index $aux2." )

  // </editor-fold>

  val ( leftDisjunct, leftContext ) = leftPremise focus aux1
  val ( rightDisjunct, rightContext ) = rightPremise focus aux2

  val formula = Or( leftDisjunct, rightDisjunct )

  def endSequent = formula +: ( leftContext ++ rightContext )

  def mainIndices = Seq( Ant( 0 ) )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  def name = "∨:l"

  def getLeftOccConnector = new OccConnector(
    endSequent,
    leftPremise,
    Seq( aux1 ) +: ( ( leftPremise.indicesSequent delete aux1 map { Seq.apply( _ ) } ) ++ ( rightPremise delete aux2 map { i => Seq() } ) )
  )

  def getRightOccConnector = new OccConnector(
    endSequent,
    rightPremise,
    Seq( aux2 ) +: ( ( leftPremise delete aux1 map { i => Seq() } ) ++ ( rightPremise.indicesSequent delete aux2 map { Seq.apply( _ ) } ) )
  )
}

object OrLeftRule {
  /**
   * Convenience constructor for ∨:r that, given formulas on the left, will automatically pick their respective first occurrences.
   *
   * @param leftSubProof
   * @param A
   * @param rightSubProof
   * @param B
   * @return
   */
  def apply( leftSubProof: LKProof, A: HOLFormula, rightSubProof: LKProof, B: HOLFormula ): OrLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val i = leftPremise.antecedent indexOf A
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create OrLeftRule: Aux formula $A not found in antecedent of $leftPremise." )

    val j = rightPremise.antecedent indexOf B

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create OrLeftRule: Aux formula $B not found in succedent of $rightPremise." )

    new OrLeftRule( leftSubProof, Ant( i ), rightSubProof, Ant( j ) )
  }

  /**
   * Convenience constructor for ∨:r that, given a proposed main formula A ∨ B, will attempt to create an inference with this main formula.
   *
   * @param leftSubProof
   * @param rightSubProof
   * @param F
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, F: HOLFormula ): OrLeftRule = F match {
    case Or( f, g ) => apply( leftSubProof, f, rightSubProof, g )
    case _          => throw new LKRuleCreationException( s"Cannot create OrLeftRule: Proposed main formula $F is not a disjunction." )
  }
}

/**
 * An LKProof ending with a disjunction on the right:
 *
 *         (π)
 *     Γ :- Δ, A, B
 *    --------------
 *     Γ :- Δ, A ∨ B
 *
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class OrRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof {

  // <editor-fold desc="Sanity checks">

  ( aux1, aux2 ) match {
    case ( Suc( _ ), Suc( _ ) ) =>
    case _                      => throw new LKRuleCreationException( s"Cannot create ContractionRightRule: One of $aux1 and $aux2 is in the antecedent." )
  }

  if ( aux1 == aux2 )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Indices of aux formulas are equal." )

  if ( !( premise isDefinedAt aux1 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Sequent $premise is not defined at index $aux1." )

  if ( !( premise isDefinedAt aux2 ) )
    throw new LKRuleCreationException( s"Cannot create ContractionRightRule: Sequent $premise is not defined at index $aux2." )
  // </editor-fold>

  val leftDisjunct = premise( aux1 )
  val rightDisjunct = premise( aux2 )
  val formula = Or( leftDisjunct, rightDisjunct )
  val ( a1, a2 ) = if ( aux1 <= aux2 ) ( aux1, aux2 ) else ( aux2, aux1 )

  val newContext = premise.focus( a2 )._2.focus( a1 )._2

  // <editor-fold desc="Overrides">

  override def endSequent = newContext :+ formula

  private val n = endSequent.succedent.length - 1

  override def mainIndices = Seq( Suc( n ) )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∨:r"

  override def getOccConnector = new OccConnector(
    endSequent,
    premise,
    ( premise.indicesSequent delete a2 delete a1 map { i => Seq( i ) } ) :+ Seq( aux1, aux2 )
  )

  // </editor-fold>
}

object OrRightRule {
  /**
   * Convenience constructor for ∨:r that, given two formulas on the right, will automatically pick the respective first instances of these formulas.
   *
   * @param subProof
   * @param A
   * @param B
   * @return
   */
  def apply( subProof: LKProof, A: HOLFormula, B: HOLFormula ): OrRightRule = {
    val premise = subProof.endSequent
    val i = premise.succedent indexOf A
    if ( i == -1 )
      throw new LKRuleCreationException( s"Cannot create OrRightRule: Aux formula $A not found in succedent of $premise." )

    val j =
      if ( A == B )
        premise.succedent indexOf ( B, i + 1 )
      else
        premise.succedent indexOf B

    if ( j == -1 )
      throw new LKRuleCreationException( s"Cannot create OrRightRule: Aux formula $B not found in succedent of $premise." )

    new OrRightRule( subProof, Suc( i ), Suc( j ) )
  }

  /**
   * Convenience constructor for ∨:r that, given a proposed main formula A ∨ B, will attempt to create an inference with this main formula.
   *
   * @param subProof
   * @param F
   * @return
   */
  def apply( subProof: LKProof, F: HOLFormula ): OrRightRule = F match {
    case Or( f, g ) => apply( subProof, f, g )
    case _          => throw new LKRuleCreationException( s"Cannot create OrRightRule: Proposed main formula $F is not a disjunction." )
  }
}
// </editor-fold>

/**
 * This class models the connection of formula occurrences between two sequents in a proof.
 *
 */
class OccConnector( val lowerSequent: HOLSequent, val upperSequent: HOLSequent, val parentsSequent: Sequent[Seq[SequentIndex]] ) {
  outer =>

  val childrenSequent = upperSequent.indicesSequent map { i => parentsSequent.indicesWhere( is => is contains i ) }

  /**
   * Given a SequentIndex for the lower sequent, this returns the list of parents of that occurrence in the upper sequent (if defined).
   *
   * @param idx
   * @return
   */
  def parents( idx: SequentIndex ): Seq[SequentIndex] = parentsSequent( idx )

  /**
   * Given a SequentIndex for the upper sequent, this returns the list of children of that occurrence in the lower sequent (if defined).
   *
   * @param idx
   * @return
   */
  def children( idx: SequentIndex ): Seq[SequentIndex] = childrenSequent( idx )

  def *( that: OccConnector ) = {
    val newAnt = for ( is <- parentsSequent.antecedent; i <- is ) yield that.parents( i )

    val newSuc = for ( is <- parentsSequent.succedent; i <- is ) yield that.parents( i )

    new OccConnector( this.lowerSequent, that.upperSequent, Sequent( newAnt, newSuc ) )
  }
}

object prettyString {
  /**
   * Produces a console-readable string representation of the lowermost rule.
   *
   * @param p The rule to be printed.
   * @return
   */
  def apply( p: LKProof ): String = p match {

    case InitialSequent( seq ) =>
      produceString( "", seq.toString, p.name )

    case UnaryLKProof( endSequent, subProof ) =>
      val upperString = sequentToString( subProof.endSequent, p.auxIndices.head )
      val lowerString = sequentToString( endSequent, p.mainIndices )
      produceString( upperString, lowerString, p.name )

    case BinaryLKProof( endSequent, leftSubproof, rightSubProof ) =>
      val upperString = sequentToString( leftSubproof.endSequent, p.auxIndices.head ) +
        "    " +
        sequentToString( rightSubProof.endSequent, p.auxIndices.tail.head )

      val lowerString = sequentToString( endSequent, p.mainIndices )
      produceString( upperString, lowerString, p.name )
  }

  private def produceString( upperString: String, lowerString: String, ruleName: String ): String = {

    val n = Math.max( upperString.length, lowerString.length ) + 2
    val line = "-" * n
    val ( upperDiff, lowerDiff ) = ( n - upperString.length, n - lowerString.length )

    val upperNew = " " * Math.floor( upperDiff / 2 ).toInt + upperString + " " * Math.ceil( upperDiff / 2 ).toInt
    val lowerNew = " " * Math.floor( lowerDiff / 2 ).toInt + lowerString + " " * Math.ceil( lowerDiff / 2 ).toInt

    upperNew + "\n" + line + ruleName + "\n" + lowerNew
  }

  private def sequentToString( sequent: HOLSequent, auxFormulas: Seq[SequentIndex] ): String = {
    val stringSequent = sequent map { _.toString() }
    auxFormulas.foldLeft( stringSequent ) { ( acc, i ) =>
      val currentString = acc( i )
      val newString = "[" + currentString + "]"
      acc.updated( i, newString )
    }.toString

  }
}