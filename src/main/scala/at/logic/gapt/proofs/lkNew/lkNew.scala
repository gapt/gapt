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
  def mainFormulas: Seq[SequentIndex]

  /**
   * A list of SequentIndices denoting the auxiliary formula(s) of the rule.
   *
   * @return
   */
  def auxFormulas: Seq[Seq[SequentIndex]]

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
}

// <editor-fold desc="Axioms">

/**
 * An LKProof consisting of a single sequent:
 *
 *     --------ax
 *      Γ :- Δ
 *
 * @param seq The sequent Γ :- Δ.
 */
class InitialSequent( seq: HOLSequent ) extends LKProof {
  def this( ant: Seq[HOLFormula], suc: Seq[HOLFormula] ) {
    this( Sequent( ant, suc ) )
  }

  override def name = "ax"

  override def mainFormulas = seq.indices

  override def auxFormulas = Seq()

  override def endSequent = seq

  override def subProofs = Seq()
}

object InitialSequent {
  def apply( seq: HOLSequent ): InitialSequent = new InitialSequent( seq )

  def apply( ant: Seq[HOLFormula], suc: Seq[HOLFormula] ): InitialSequent = apply( HOLSequent( ant, suc ) )
}

/**
 * An LKProof introducing ⊤ on the right:
 *
 *       --------⊤:r
 *         :- ⊤
 */
case object TopAxiom extends InitialSequent( Nil, Seq( Top() ) ) { override def name: String = "⊤:r" }

/**
 * An LKProof introducing ⊥ on the left:
 *
 *       --------⊥:l
 *         ⊥ :-
 */
case object BottomAxiom extends InitialSequent( Seq( Bottom() ), Nil ) { override def name: String = "⊥:l" }

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
case class LogicalAxiom( A: HOLAtom ) extends InitialSequent( HOLSequent( Seq( A ), Seq( A ) ) )

/**
 * An LKProof consisting of a reflexivity axiom:
 *
 *    ------------case Suc( 0 )                               => Seq( aux1, aux2 )
 *      :- s = s
 *
 * with s a term.
 *
 * @param s The term s.
 */
case class ReflexivityAxiom( s: LambdaExpression ) extends InitialSequent( HOLSequent( Seq(), Seq( Eq( s, s ) ) ) )

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

  val formula = premise( aux1 )
  val ( a1, a2 ) = if ( aux1 <= aux2 ) ( aux1, aux2 ) else ( aux2, aux1 )

  val newContext = premise.focus( a2 )._2.focus( a1 )._2

  // <editor-fold desc="Overrides">

  override def endSequent = formula +: newContext

  override def mainFormulas = Seq( Ant( 0 ) )

  override def auxFormulas = Seq( Seq( aux1, aux2 ) )

  override def subProofs = Seq( subProof )

  override def name = "c:l"

  override def getOccConnector = new OccConnector {

    def children( idx: SequentIndex ): Seq[SequentIndex] =
      ( ( a1, a2 ): @unchecked ) match {
        case ( Ant( i ), Ant( j ) ) =>
          idx match {
            case Ant( k ) if k < i                   => Seq( Ant( k + 1 ) )
            case Ant( `i` )                          => Seq( Ant( 0 ) )
            case Ant( k ) if k < j                   => Seq( Ant( k ) )
            case Ant( `j` )                          => Seq( Ant( 0 ) )
            case Ant( k ) if premise isDefinedAt idx => Seq( Ant( k - 1 ) )
            case Ant( _ )                            => throw new NoSuchElementException( s"Sequent $premise not defined at index $idx." )

            case Suc( k ) if premise isDefinedAt idx => Seq( idx )
            case Suc( _ )                            => throw new NoSuchElementException( s"Sequent $premise not defined at index $idx." )
          }
      }

    def parents( idx: SequentIndex ): Seq[SequentIndex] =
      ( ( a1, a2 ): @unchecked ) match {
        case ( Ant( i ), Ant( j ) ) =>
          idx match {
            case Ant( 0 )                               => Seq( aux1, aux2 )
            case Ant( k ) if k <= i                     => Seq( Ant( k - 1 ) )
            case Ant( k ) if k < j                      => Seq( Ant( k ) )
            case Ant( k ) if endSequent isDefinedAt idx => Seq( Ant( k + 1 ) )
            case Ant( _ )                               => throw new NoSuchElementException( s"Sequent $endSequent not defined at index $idx." )

            case Suc( _ ) if endSequent isDefinedAt idx => Seq( idx )
            case Suc( _ )                               => throw new NoSuchElementException( s"Sequent $endSequent not defined at index $idx." )
          }
      }
  }

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

  val formula = premise( aux1 )
  val ( a1, a2 ) = if ( aux1 <= aux2 ) ( aux1, aux2 ) else ( aux2, aux1 )

  val newContext = premise.focus( a2 )._2.focus( a1 )._2

  // <editor-fold desc="Overrides">

  override def endSequent = newContext :+ formula

  private val n = endSequent.succedent.length

  override def mainFormulas = Seq( Suc( n ) )

  override def auxFormulas = Seq( Seq( aux1, aux2 ) )

  override def subProofs = Seq( subProof )

  override def name = "c:r"

  override def getOccConnector = new OccConnector {

    def children( idx: SequentIndex ): Seq[SequentIndex] =
      ( ( a1, a2 ): @unchecked ) match {
        case ( Ant( i ), Ant( j ) ) =>
          idx match {
            case Suc( k ) if k < i                   => Seq( Suc( k ) )
            case Suc( `i` )                          => Seq( Suc( n ) )
            case Suc( k ) if k < j                   => Seq( Suc( k - 1 ) )
            case Suc( `j` )                          => Seq( Suc( n ) )
            case Suc( k ) if premise isDefinedAt idx => Seq( Suc( k - 2 ) )
            case Suc( _ )                            => throw new NoSuchElementException( s"Sequent $premise not defined at index $idx." )

            case Ant( k ) if premise isDefinedAt idx => Seq( idx )
            case Ant( _ )                            => throw new NoSuchElementException( s"Sequent $premise not defined at index $idx." )
          }
      }

    def parents( idx: SequentIndex ): Seq[SequentIndex] =
      ( ( a1, a2 ): @unchecked ) match {
        case ( Ant( i ), Ant( j ) ) =>
          idx match {
            case Suc( k ) if k < i                      => Seq( Suc( k ) )
            case Suc( k ) if k < j                      => Seq( Suc( k + 1 ) )
            case Suc( k ) if k < n                      => Seq( Suc( k + 2 ) )
            case Suc( `n` )                             => Seq( aux1, aux2 )
            case Suc( _ )                               => throw new NoSuchElementException( s"Sequent $endSequent not defined at index $idx." )

            case Ant( _ ) if endSequent isDefinedAt idx => Seq( idx )
            case Ant( _ )                               => throw new NoSuchElementException( s"Sequent $endSequent not defined at index $idx." )
          }
      }
  }

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

// </editor-fold>

/**
 * This class models the connection of formula occurrences between two sequents in a proof.
 *
 */
abstract class OccConnector {
  outer => // I don't know what this does, but it works.
  /**
   * Given a SequentIndex for the lower sequent, this returns the list of parents of that occurrence in the upper sequent (if defined).
   *
   * @param i
   * @return
   */
  def parents( i: SequentIndex ): Seq[SequentIndex]

  /**
   * Given a SequentIndex for the upper sequent, this returns the list of children of that occurrence in the lower sequent (if defined).
   *
   * @param i
   * @return
   */
  def children( i: SequentIndex ): Seq[SequentIndex]

  def *( that: OccConnector ) = new OccConnector {
    def parents( i: SequentIndex ) =
      outer.parents( i ) flatMap that.parents
    def children( i: SequentIndex ) = that.children( i ) flatMap outer.children
  }
}