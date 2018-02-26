package at.logic.gapt.proofs.nd

import at.logic.gapt.expr._
import at.logic.gapt.proofs.IndexOrFormula.{ IsFormula, IsIndex }
import at.logic.gapt.proofs._

import scala.collection.mutable

abstract class NDProof extends SequentProof[Formula, NDProof] {

  protected def NDRuleCreationException( message: String ): NDRuleCreationException =
    new NDRuleCreationException( longName, message )

  /**
   * The end-sequent of the rule.
   */
  final def endSequent = conclusion

  /**
   * Checks whether indices are in the right place and premise is defined at all of them.
   *
   * @param premise The sequent to be checked.
   * @param antecedentIndices Indices that should be in the antecedent.
   */
  protected def validateIndices( premise: HOLSequent, antecedentIndices: Seq[SequentIndex] ): Unit = {
    val antSet = mutable.HashSet[SequentIndex]()

    for ( i <- antecedentIndices ) i match {
      case Ant( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw NDRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( antSet contains i )
          throw NDRuleCreationException( s"Duplicate index $i for sequent $premise." )

        antSet += i

      case Suc( _ ) => throw NDRuleCreationException( s"Index $i should be in the antecedent." )
    }
  }
}

/**
 * An NDProof deriving a sequent from another sequent:
 * <pre>
 *        (π)
 *      Γ :- A
 *    ----------
 *     Γ' :- A'
 * </pre>
 */
abstract class UnaryNDProof extends NDProof {
  /**
   * The immediate subproof of the rule.
   *
   * @return
   */
  def subProof: NDProof

  /**
   * The object connecting the lower and upper sequents.auxFormulas.
   *
   * @return
   */
  def getSequentConnector: SequentConnector = occConnectors.head

  /**
   * The upper sequent of the rule.
   *
   * @return
   */
  def premise = subProof.endSequent

  override def immediateSubProofs = Seq( subProof )
}

object UnaryNDProof {
  def unapply( p: UnaryNDProof ) = Some( p.endSequent, p.subProof )
}

/**
 * An NDProof deriving a sequent from two other sequents:
 * <pre>
 *     (π1)     (π2)
 *    Γ :- A   Γ' :- A'
 *   ------------------
 *        Π :- B
 * </pre>
 */
abstract class BinaryNDProof extends NDProof {
  /**
   * The immediate left subproof of the rule.
   *
   * @return
   */
  def leftSubProof: NDProof

  /**
   * The immediate right subproof of the rule.
   *
   * @return
   */
  def rightSubProof: NDProof

  /**
   * The object connecting the lower and left upper sequents.
   *
   * @return
   */
  def getLeftSequentConnector: SequentConnector = occConnectors.head

  /**
   * The object connecting the lower and right upper sequents.
   *
   * @return
   */
  def getRightSequentConnector: SequentConnector = occConnectors.tail.head

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

  override def immediateSubProofs = Seq( leftSubProof, rightSubProof )
}

object BinaryNDProof {
  def unapply( p: BinaryNDProof ) = Some( p.endSequent, p.leftSubProof, p.rightSubProof )
}

/**
 * An NDProof deriving a sequent from three other sequents:
 * <pre>
 *     (π1)        (π2)        (π3)
 *    Γ1 :- A1   Γ2 :- A2   Γ3 :- A3
 *   --------------------------------
 *               Π :- B
 * </pre>
 */
abstract class TernaryNDProof extends NDProof {
  /**
   * The immediate left subproof of the rule.
   *
   * @return
   */
  def leftSubProof: NDProof

  /**
   * The immediate middle subproof of the rule.
   *
   * @return
   */
  def middleSubProof: NDProof

  /**
   * The immediate right subproof of the rule.
   *
   * @return
   */
  def rightSubProof: NDProof

  /**
   * The object connecting the lower and left upper sequents.
   *
   * @return
   */
  def getLeftSequentConnector: SequentConnector = occConnectors( 0 )

  /**
   * The object connecting the lower and middle upper sequents.
   *
   * @return
   */
  def getMiddleSequentConnector: SequentConnector = occConnectors( 1 )

  /**
   * The object connecting the lower and right upper sequents.
   *
   * @return
   */
  def getRightSequentConnector: SequentConnector = occConnectors( 2 )

  /**
   * The left upper sequent of the rule.
   *
   * @return
   */
  def leftPremise = leftSubProof.endSequent

  /**
   * The middle upper sequent of the rule.
   *
   * @return
   */
  def middlePremise = middleSubProof.endSequent

  /**
   * The right upper sequent of the rule.
   *
   * @return
   */
  def rightPremise = rightSubProof.endSequent

  override def immediateSubProofs = Seq( leftSubProof, middleSubProof, rightSubProof )
}

object TernaryNDProof {
  def unapply( p: TernaryNDProof ) = Some( p.endSequent, p.leftSubProof, p.middleSubProof, p.rightSubProof )
}

trait CommonRule extends NDProof with ContextRule[Formula, NDProof]

/**
 * Use this trait for rules that use eigenvariables.
 *
 */
trait Eigenvariable {
  def eigenVariable: Var
}

/**
 * An NDProof consisting of a single sequent:
 * <pre>
 *     --------ax
 *      Γ :- A
 * </pre>
 */
abstract class InitialSequent extends NDProof {

  override def mainIndices = endSequent.indices

  override def auxIndices = Seq()

  override def immediateSubProofs = Seq()

  override def occConnectors = Seq()
}

object InitialSequent {
  def unapply( proof: InitialSequent ) = Some( proof.endSequent )
}

/**
 * An NDProof ending with weakening:
 * <pre>
 *        (π)
 *       Γ :- B
 *     ---------wkn
 *     A, Γ :- B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningRule( subProof: NDProof, formula: Formula )
  extends UnaryNDProof with CommonRule {
  override def auxIndices = Seq( Seq() )
  override def name = "wkn"
  def mainFormula = formula

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object WeakeningRule extends ConvenienceConstructor( "WeakeningRule" ) {

  /**
   * Convenience constructor for ax, taking a context.
   * Applies the axiom rule followed by 0 or more weakenings.
   * <pre>
   *      (π)
   *     Γ :- B
   *    ---------------------wkn*
   *     A1, ..., An, Γ :- B
   * </pre>
   *
   * @param subProof The subproof π.
   * @param formulas The formulas A1, ..., An
   * @return
   */
  def apply( subProof: NDProof, formulas: Seq[Formula] ): NDProof = {

    formulas.foldLeft[NDProof]( subProof ) { ( ant, c ) =>
      WeakeningRule( ant, c )
    }
  }
}

/**
 * An NDProof ending with a contraction:
 * <pre>
 *         (π)
 *     A, A, Γ :- B
 *    --------------ctr
 *      A, Γ :- B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionRule( subProof: NDProof, aux1: SequentIndex, aux2: SequentIndex )
  extends UnaryNDProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ) )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw NDRuleCreationException( s"Auxiliary formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  val mainFormula = premise( aux1 )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "ctr"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ContractionRule extends ConvenienceConstructor( "ContractionRule" ) {
  /**
   * Convenience constructor for ctr that, given a formula to contract, will automatically pick the
   * first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   */
  def apply( subProof: NDProof, f: Formula ): ContractionRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( f, f ), Suc( 0 ) )

    val p = ContractionRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
    assert( p.mainFormula == f )
    p
  }

}

/**
 * An NDProof consisting of a logical axiom:
 * <pre>
 *    --------ax
 *     A :- A
 * </pre>
 *
 * @param A The formula A.
 */
case class LogicalAxiom( A: Formula ) extends InitialSequent {
  override def name = "ax"
  override def conclusion = NDSequent( Seq( A ), A )
  def mainFormula = A
}

object LogicalAxiom extends ConvenienceConstructor( "LogicalAxiom" ) {

  /**
   * Convenience constructor for ax, taking a context.
   * Applies the axiom rule followed by 0 or more weakenings.
   * <pre>
   *    --------ax
   *     A :- A
   *    -----------wkn*
   *     Γ, A :- A
   * </pre>
   *
   * @param A The atom a.
   * @param context The context Γ.
   * @return
   */
  def apply( A: Formula, context: Seq[Formula] ): NDProof = {

    context.foldLeft[NDProof]( LogicalAxiom( A ) ) { ( ant, c ) =>
      WeakeningRule( ant, c )
    }
  }
}

/**
 * An NDProof ending with elimination of the right conjunct:
 * <pre>
 *         (π)
 *      Γ :- A ∧ B
 *    --------------∧:e1
 *        Γ :- A
 * </pre>
 *
 * @param subProof The subproof π.
 */
case class AndElim1Rule( subProof: NDProof )
  extends UnaryNDProof with CommonRule {

  val conjunction = premise( Suc( 0 ) )

  val mainFormula = conjunction match {
    case And( leftConjunct, _ ) => leftConjunct
    case _ =>
      throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
  }

  override def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def name = "∧:e1"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with elimination of the left conjunct:
 * <pre>
 *         (π)
 *      Γ :- A ∧ B
 *    --------------∧:e2
 *        Γ :- B
 * </pre>
 *
 * @param subProof The subproof π.
 */
case class AndElim2Rule( subProof: NDProof )
  extends UnaryNDProof with CommonRule {

  val conjunction = premise( Suc( 0 ) )

  val mainFormula = conjunction match {
    case And( _, rightConjunct ) => rightConjunct
    case _ =>
      throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
  }

  override def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def name = "∧:e2"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with a conjunction on the right:
 * <pre>
 *    (π1)      (π2)
 *   Γ :- A    Π :- B
 * --------------------∧:i
 *     Γ, Π :- A∧B
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,.
 */
case class AndIntroRule( leftSubProof: NDProof, rightSubProof: NDProof )
  extends BinaryNDProof with CommonRule {

  val leftConjunct = leftPremise( Suc( 0 ) )
  val rightConjunct = rightPremise( Suc( 0 ) )

  val mainFormula = And( leftConjunct, rightConjunct )

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "∧:i"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with elimination of a disjunction:
 * <pre>
 *     (π1)         (π2)         (π3)
 *   Γ :- A∨B   Π, A :- C    Δ, B :- C
 *  ------------------------------------∨:e
 *           Γ, Π, Δ  :- C
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param middleSubProof The proof π,,2,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,3,,.
 * @param aux2 The index of B.
 */
case class OrElimRule(
    leftSubProof:   NDProof,
    middleSubProof: NDProof, aux1: SequentIndex,
    rightSubProof: NDProof, aux2: SequentIndex )
  extends TernaryNDProof with CommonRule {

  validateIndices( middlePremise, Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ) )

  val leftDisjunct = middlePremise( aux1 )
  val rightDisjunct = rightPremise( aux2 )

  val disjunction = leftPremise( Suc( 0 ) )

  require(
    disjunction == Or( leftDisjunct, rightDisjunct ),
    throw NDRuleCreationException( s"Formula $disjunction is not a disjunction of $leftDisjunct and $rightDisjunct." ) )

  val middleC = middlePremise( Suc( 0 ) )
  val rightC = rightPremise( Suc( 0 ) )

  val mainFormula = if ( middleC == rightC ) middleC else
    throw NDRuleCreationException( s"Formulas $middleC an $rightC are not the same." )

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( aux1, Suc( 0 ) ), Seq( aux2, Suc( 0 ) ) )

  override def name = "∨:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object OrElimRule extends ConvenienceConstructor( "OrElimRule" ) {

  /**
   * Convenience constructor for ∨:e.
   * Given only the subproofs, it will attempt to create an inference with this.
   *
   * @param leftSubProof The left subproof.
   * @param middleSubProof The middle subproof.
   * @param rightSubProof The right subproof.
   * @return
   */
  def apply( leftSubProof: NDProof, middleSubProof: NDProof, rightSubProof: NDProof ): OrElimRule = {
    val disjunction = leftSubProof.endSequent( Suc( 0 ) )

    val ( leftDisjunct, rightDisjunct ) = disjunction match {
      case Or( f, g ) => ( f, g )
      case _          => throw NDRuleCreationException( s"Formula $disjunction is not a disjunction." )
    }

    val ( middlePremise, rightPremise ) = ( middleSubProof.endSequent, rightSubProof.endSequent )

    val ( middleIndices, _ ) = findAndValidate( middlePremise )( Seq( leftDisjunct ), Suc( 0 ) )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( rightDisjunct ), Suc( 0 ) )

    new OrElimRule( leftSubProof, middleSubProof, Ant( middleIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
  }
}

/**
 * An NDProof ending with introduction of a disjunction, with a new formula as the right disjunct:
 * <pre>
 *       (π)
 *      Γ :- A
 *    ------------∨:i1
 *     Γ :- A ∨ B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param rightDisjunct The formula B.
 */
case class OrIntro1Rule( subProof: NDProof, rightDisjunct: Formula )
  extends UnaryNDProof with CommonRule {

  val leftDisjunct = premise( Suc( 0 ) )
  val mainFormula = Or( leftDisjunct, rightDisjunct )

  override def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def name = "∨:i1"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with introduction of a disjunction, with a new formula as the left disjunct:
 * <pre>
 *       (π)
 *      Γ :- A
 *    ------------∨:i2
 *     Γ :- B ∨ A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param leftDisjunct The formula B.
 */
case class OrIntro2Rule( subProof: NDProof, leftDisjunct: Formula )
  extends UnaryNDProof with CommonRule {

  val rightDisjunct = premise( Suc( 0 ) )
  val mainFormula = Or( leftDisjunct, rightDisjunct )

  override def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def name = "∨:i2"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with elimination of an implication:
 * <pre>
 *   (π1)        (π2)
 *  Γ :- A→B    Π :- A
 * --------------------→:e
 *     Γ, Π :- B
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,.
 */
case class ImpElimRule( leftSubProof: NDProof, rightSubProof: NDProof )
  extends BinaryNDProof with CommonRule {

  val implication = leftPremise( Suc( 0 ) )
  val antecedent = rightPremise( Suc( 0 ) )

  val mainFormula = implication match {
    case Imp( `antecedent`, consequent ) => consequent
    case Imp( _, _ ) =>
      throw NDRuleCreationException( s"Proposed main formula $antecedent is not the antecedent of $implication." )
    case _ =>
      throw NDRuleCreationException( s"Proposed main formula $implication is not an implication." )
  }

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "→:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with introduction of an implication:
 * <pre>
 *         (π)
 *      A, Γ :- B
 *    ------------→:i
 *     Γ :- A → B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux The index of A.
 */
case class ImpIntroRule( subProof: NDProof, aux: SequentIndex )
  extends UnaryNDProof with CommonRule {

  validateIndices( premise, Seq( aux ) )

  val impPremise = premise( aux )
  val impConclusion = premise( Suc( 0 ) )
  val mainFormula = Imp( impPremise, impConclusion )

  override def auxIndices = Seq( Seq( aux, Suc( 0 ) ) )

  override def name = "→:i"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ImpIntroRule extends ConvenienceConstructor( "ImpIntroRule" ) {

  /**
   * Convenience constructor for →:i.
   * The aux formula can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param impPremise Index of the premise of the implication or the premise itself.
   * @return
   */
  def apply( subProof: NDProof, impPremise: IndexOrFormula ): ImpIntroRule = {
    val premise = subProof.endSequent

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( impPremise ), Suc( 0 ) )

    new ImpIntroRule( subProof, Ant( antIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:i
   * If the subproof has precisely one element in the antecedent of its premise, this element will be the aux index.
   *
   * @param subProof The subproof.
   * @return
   */

  def apply( subProof: NDProof ): ImpIntroRule = {
    val premise = subProof.endSequent

    if ( premise.antecedent.size == 1 ) apply( subProof, Ant( 0 ) )
    else if ( premise.antecedent.size == 0 )
      throw NDRuleCreationException( s"Antecedent of $premise doesn't contain any elements." )
    else throw NDRuleCreationException( s"Antecedent of $premise has more than one element, " +
      s"the formula serving as antecedent of the implication should be specified." )
  }

}

/**
 * An NDProof ending with elimination of a negation:
 * <pre>
 *   (π1)      (π2)
 *  Γ :- ¬A    Π :- A
 * -------------------¬:e
 *     Γ, Π :- ⊥
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,.
 */
case class NegElimRule( leftSubProof: NDProof, rightSubProof: NDProof )
  extends BinaryNDProof with CommonRule {

  val negatedFormula = leftPremise( Suc( 0 ) )
  val formula = rightPremise( Suc( 0 ) )

  val mainFormula = if ( negatedFormula == Neg( formula ) ) Bottom() else
    throw NDRuleCreationException( s"Formula $negatedFormula is not the negation of $formula." )

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "¬:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with introduction of a negation:
 * <pre>
 *         (π)
 *     A, Γ :- ⊥
 *    -----------¬:i
 *     Γ :- ¬A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux The index of A.
 */
case class NegIntroRule( subProof: NDProof, aux: SequentIndex )
  extends UnaryNDProof with CommonRule {

  validateIndices( premise, Seq( aux ) )

  val bottom = premise( Suc( 0 ) )

  require( bottom == Bottom(), s"Formula $bottom is not ⊥." )

  val formula = premise( aux )
  val mainFormula = Neg( formula )

  override def auxIndices = Seq( Seq( aux, Suc( 0 ) ) )

  override def name = "¬:i"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object NegIntroRule extends ConvenienceConstructor( "NegIntroRule" ) {

  /**
   * Convenience constructor for ¬:i.
   * The aux formula can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param negation Index of the negation or the negation itself.
   * @return
   */
  def apply( subProof: NDProof, negation: IndexOrFormula ): NegIntroRule = {
    val premise = subProof.endSequent

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( negation ), Suc( 0 ) )

    new NegIntroRule( subProof, Ant( antIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for ¬:i.
   * If the subproof has precisely one element in the antecedent of its premise, this element will be the aux index.
   *
   * @param subProof The subproof.
   * @return
   */
  def apply( subProof: NDProof ): NegIntroRule = {
    val premise = subProof.endSequent

    if ( premise.antecedent.size == 1 ) apply( subProof, Ant( 0 ) )
    else if ( premise.antecedent.size == 0 )
      throw NDRuleCreationException( s"Antecedent of $premise doesn't contain any elements." )
    else throw NDRuleCreationException(
      s"Antecedent of $premise has more than one element, the formula to be negated should be specified." )

  }
}

/**
 * An NDProof that is the introduction of ⊤:
 * <pre>
 *    ------⊤:i
 *     :- ⊤
 * </pre>
 */
case class TopIntroRule() extends InitialSequent {

  def mainFormula = Top()

  def conclusion = NDSequent( Seq(), mainFormula )

  override def name = "⊤:i"
}

/**
 * An NDProof eliminating ⊥:
 * <pre>
 *       (π)
 *     Γ :- ⊥
 *    --------⊥:e
 *     Γ :- A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param mainFormula The formula A.
 */
case class BottomElimRule( subProof: NDProof, mainFormula: Formula )
  extends UnaryNDProof with CommonRule {

  val bottom = premise( Suc( 0 ) )

  require( bottom == Bottom(), s"Formula $bottom is not ⊥." )

  override def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def name = "⊥:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with a universal quantifier introduction:
 * <pre>
 *           (π)
 *      Γ :- A[x\α]
 *     -------------∀:i
 *      Γ :- ∀x.A
 * </pre>
 * This rule is only applicable if the eigenvariable condition is satisfied: α must not occur freely in Γ.
 *
 * @param subProof The proof π.
 * @param eigenVariable The variable α.
 * @param quantifiedVariable The variable x.
 */
case class ForallIntroRule( subProof: NDProof, eigenVariable: Var, quantifiedVariable: Var )
  extends UnaryNDProof with CommonRule with Eigenvariable {

  val ( auxFormula, context ) = premise focus Suc( 0 )

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw NDRuleCreationException( s"Eigenvariable condition is violated: $context contains $eigenVariable" )

  def subFormula = BetaReduction.betaNormalize( Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  if ( BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) != auxFormula )
    throw NDRuleCreationException( s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = " +
      BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) )
      + s", but is $auxFormula." )

  def mainFormula = BetaReduction.betaNormalize( All( quantifiedVariable, subFormula ) )

  override def name = "∀:i"

  def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallIntroRule extends ConvenienceConstructor( "ForallIntroRule" ) {

  /**
   * Convenience constructor for ∀:i that, given a main formula and an eigenvariable, will try to
   * construct an inference with that instantiation.
   *
   * @param subProof      The subproof.
   * @param mainFormula   The formula to be inferred. Must be of the form ∀x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: NDProof, mainFormula: Formula, eigenVariable: Var ): ForallIntroRule = {
    if ( freeVariables( mainFormula ) contains eigenVariable ) {
      throw NDRuleCreationException( s"Illegal main formula: Eigenvariable $eigenVariable is free in $mainFormula." )
    } else mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = Substitution( v, eigenVariable )( subFormula )

        val premise = subProof.endSequent

        val ( _, indices ) = findAndValidate( premise )( Seq(), auxFormula )

        val p = ForallIntroRule( subProof, eigenVariable, v )
        assert( p.mainFormula == mainFormula )
        p

      case _ => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
    }
  }
}

/**
 * An NDProof ending with a universal quantifier elimination:
 * <pre>
 *        (π)
 *      Γ :- ∀x.A
 *     -------------∀:e
 *      Γ :- A[x\t]
 * </pre>
 *
 * @param subProof The proof π.
 * @param term The term t.
 */
case class ForallElimRule( subProof: NDProof, term: Expr )
  extends UnaryNDProof with CommonRule {

  val universal = premise( Suc( 0 ) )

  val mainFormula = universal match {
    case All( v, subFormula ) => Substitution( v, term )( subFormula )
    case _ =>
      throw NDRuleCreationException( s"Proposed main formula $universal is not universally quantified." )
  }

  override def name = "∀:e"

  def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallElimBlock {

  /**
   * Applies the ForallElim-rule n times.
   *
   * The rule:
   * <pre>
   *              (π)
   *    Γ :- ∀x1,..,xN.A
   * ---------------------------------- (∀_e x n)
   *     Γ :- A[x1\t1,...,xN\tN]
   *
   * where t1,...,tN are terms.
   * </pre>
   *
   * @param subProof The proof π with (Γ :- ∀x1,..,xN.A) as the bottommost sequent.
   * @param terms The list of terms with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * ∀x1,..,xN.A indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: NDProof, terms: Seq[Expr] ): NDProof =
    terms.foldLeft( subProof )( ( acc, t ) => nd.ForallElimRule( acc, t ) )

}

/**
 * An NDProof ending with an existential quantifier introduction:
 * <pre>
 *        (π)
 *      Γ :- A[x\t]
 *     ------------∃:i
 *      Γ :- ∃x.A
 * </pre>
 *
 * @param subProof The proof π.
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ExistsIntroRule( subProof: NDProof, A: Formula, term: Expr, v: Var )
  extends UnaryNDProof with CommonRule {

  if ( premise( Suc( 0 ) ) != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw NDRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( Suc( 0 ) )}." )

  val mainFormula = BetaReduction.betaNormalize( Ex( v, A ) )

  override def name = "∃:i"

  def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ExistsIntroRule extends ConvenienceConstructor( "ExistsIntroRule" ) {

  /**
   * Convenience constructor for ∃:i that, given a main formula and a term, will try to
   * construct an inference with that instantiation.
   *
   * @param subProof    The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A.
   * @param term        A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: NDProof, mainFormula: Formula, term: Expr ): ExistsIntroRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case Ex( v, subFormula ) =>

        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )

        if ( premise( Suc( 0 ) ) == auxFormula ) {
          val p = ExistsIntroRule( subProof, subFormula, term, v )
          assert( p.mainFormula == mainFormula )
          p
        } else throw NDRuleCreationException( s"Formula $auxFormula is not the succedent of $premise." )

      case _ => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
    }
  }

  /**
   * Convenience constructor for ∃:i that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof    The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A[t\x]. The premise must contain A[t].
   * @return
   */
  def apply( subProof: NDProof, mainFormula: Formula ): ExistsIntroRule = mainFormula match {
    case Ex( v, subFormula ) =>
      val pos = subFormula.find( v ).head
      val t = if ( subProof.endSequent( Suc( 0 ) ).isDefinedAt( pos ) )
        subProof.endSequent( Suc( 0 ) ).get( pos ).get
      else
        throw NDRuleCreationException( s"Premise is not defined at $pos." )
      val p = apply( subProof, mainFormula, t )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }
}

/**
 * An NDProof ending with an existential quantifier elimination:
 * <pre>
 *         (π1)         (π2)
 *     Γ :- ∃x.A   Π, A[x\α] :- B
 *    ----------------------------∃:e
 *        Γ, Π :- B
 * </pre>
 * This rule is only applicable if the eigenvariable condition is satisfied: α must not occur freely in Π, and B
 *
 * @param leftSubProof The proof π1.
 * @param rightSubProof The proof π2.
 * @param aux The index of A[x\α].
 * @param eigenVariable The variable α.
 */
case class ExistsElimRule( leftSubProof: NDProof, rightSubProof: NDProof, aux: SequentIndex, eigenVariable: Var )
  extends BinaryNDProof with CommonRule with Eigenvariable {

  validateIndices( rightPremise, Seq( aux ) )

  val ( existentialFormula, leftContext ) = leftPremise focus Suc( 0 )

  val ( auxFormula, rightContext ) = rightPremise focus aux

  //eigenvariable condition
  if ( freeVariables( rightContext ) contains eigenVariable )
    throw NDRuleCreationException( s"Eigenvariable condition is violated: $rightContext contains $eigenVariable" )

  val ( quantifiedVariable, subFormula ) = existentialFormula match {
    case Ex( variable, sub ) => ( variable, sub )
    case _ =>
      throw NDRuleCreationException( s"Formula $existentialFormula is not existentially quantified." )
  }

  val auxShouldBe = BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) )

  if ( auxShouldBe != auxFormula ) throw NDRuleCreationException( s"Formula $auxFormula should be $auxShouldBe." )

  val mainFormula = rightPremise( Suc( 0 ) )

  override def name = "∃:e"

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( aux, Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ExistsElimRule extends ConvenienceConstructor( "ExistsElimRule" ) {

  /**
   * Convenience constructor for ∃:e that, given an eigenvariable, will try to
   * construct an inference with that instantiation.
   *
   * @param leftSubProof The proof π1.
   * @param rightSubProof The proof π2.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( leftSubProof: NDProof, rightSubProof: NDProof, eigenVariable: Var ): ExistsElimRule = {

    val existentialFormula = leftSubProof.conclusion( Suc( 0 ) )

    existentialFormula match {
      case Ex( v, subFormula ) =>
        val auxFormula = Substitution( v, eigenVariable )( subFormula )

        val premise = rightSubProof.endSequent

        val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Suc( 0 ) )
        ExistsElimRule( leftSubProof, rightSubProof, Ant( indices( 0 ) ), eigenVariable )

      case _ => throw NDRuleCreationException( s"Formula $existentialFormula is not existentially quantified." )
    }
  }

  /**
   * Convenience constructor for ∃:e that, given only its subproofs, will try to
   * construct an inference with that formula.
   *
   * @param leftSubProof The proof π1.
   * @param rightSubProof The proof π2.
   * @return
   */
  def apply( leftSubProof: NDProof, rightSubProof: NDProof ): ExistsElimRule = {

    val existentialFormula = leftSubProof.conclusion( Suc( 0 ) )

    existentialFormula match {
      case Ex( v, subFormula ) => apply( leftSubProof, rightSubProof, v )

      case _ =>
        throw NDRuleCreationException( s"Formula $existentialFormula is not existentially quantified." )
    }
  }
}

/**
 * An NDProof consisting of an axiom from a theory:
 * <pre>
 *    --------th
 *      :- A
 * </pre>
 *
 * @param mainFormula The axiom A.
 */
case class TheoryAxiom( mainFormula: Formula ) extends InitialSequent {
  def conclusion = NDSequent( Seq(), mainFormula )
  override def name = "th"
}

/**
 * An NDProof ending with elimination of equality:
 * <pre>
 *       (π1)         (π2)
 *    Γ :- s = t    Π :- A[x\s]
 *   ------------------------------eq:e
 *          Γ,Π :- A[x\t]
 *
 * </pre>
 *
 * @param leftSubProof The subproof π1.
 * @param rightSubProof The subproof π2.
 * @param formulaA The formula A.
 * @param variablex The variable x.
 */
case class EqualityElimRule( leftSubProof: NDProof, rightSubProof: NDProof, formulaA: Formula, variablex: Var )
  extends BinaryNDProof with CommonRule {

  val eqFormula = leftPremise( Suc( 0 ) )
  val ( s, t ) = eqFormula match {
    case Eq( s, t ) => ( s, t )
    case _          => throw NDRuleCreationException( s"Formula $eqFormula is not an equation." )
  }

  val substitution1 = Substitution( variablex, s )
  val substitution2 = Substitution( variablex, t )

  val auxFormula = rightPremise( Suc( 0 ) )

  val mainFormula = if ( auxFormula == BetaReduction.betaNormalize( substitution1( formulaA ) ) )
    BetaReduction.betaNormalize( substitution2( formulaA ) )
  else if ( auxFormula == BetaReduction.betaNormalize( substitution2( formulaA ) ) )
    BetaReduction.betaNormalize( substitution1( formulaA ) )
  else
    throw NDRuleCreationException(
      s"Formula $auxFormula is not equal to $formulaA with either " +
        s"substitution $substitution1 or $substitution2 applied to it." )

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "eq:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object EqualityElimRule extends ConvenienceConstructor( "EqualityElimRule" ) {

  /**
   * Convenience constructor for eq:e.
   * Given only the subproofs, it will attempt to create an inference with this.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @return
   */
  def apply( leftSubProof: NDProof, rightSubProof: NDProof ): EqualityElimRule = {

    val eqFormula = leftSubProof.conclusion( Suc( 0 ) )
    val auxFormula = rightSubProof.conclusion( Suc( 0 ) )

    val ( s, _ ) = eqFormula match {
      case Eq( s, t ) => ( s, t )
      case _          => throw NDRuleCreationException( s"Formula $eqFormula is not an equation." )
    }

    val repContext = replacementContext.abstractTerm( auxFormula )( s )

    val formulaA = repContext.term.asInstanceOf[Formula]
    val variablex = repContext.variable.asInstanceOf[Var]

    new EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex )
  }
}

/**
 * An NDProof that consist of the introduction of an equality.
 * <pre>
 *    ----------eq:i
 *    :- t = t
 *
 * </pre>
 *
 * @param t The term t.
 */
case class EqualityIntroRule( t: Expr ) extends InitialSequent {

  override def name = "eq:i"
  override def conclusion = NDSequent( Seq(), Eq( t, t ) )
  def mainFormula = Eq( t, t )
}

/**
 * Proof that a given data type constructor c preserves a formula F:
 *
 * <pre>
 *                                  (π)
 * F(x,,1,,), F(x,,2,,), ..., F(x,,n,,), Γ :- F(c(x,,1,,,...,x,,n,,,y,,1,,,...,y,,n,,))
 * </pre>
 *
 * The variables x,,i,, and y,,i,, are eigenvariables; x,,i,, are the eigenvariables of the
 * same type as the inductive data type, y,,i,, are the other arguments of the constructor c.
 * They can come in any order in the constructor.
 *
 * @param proof  The NDProof ending in the sequent of this case.
 * @param constructor  The constructor c of the inductive data type that we're considering.
 * @param hypotheses  Indices of F(x,,1,,), ..., F(x,,n,,)
 * @param eigenVars  The eigenvariables of this case: x,,1,,, ..., x,,n,,, y,,1,,, ..., y,,n,,
 *                   (these need to correspond to the order in c)
 */
case class InductionCase( proof: NDProof, constructor: Const,
                          hypotheses: Seq[SequentIndex], eigenVars: Seq[Var] ) {
  val FunctionType( indTy, fieldTypes ) = constructor.ty
  require( fieldTypes == eigenVars.map( _.ty ) )

  val hypVars = eigenVars filter { _.ty == indTy }
  require( hypotheses.size == hypVars.size )

  hypotheses foreach { hyp =>
    require( hyp.isAnt && proof.endSequent.isDefinedAt( hyp ) )
  }

  val term = constructor( eigenVars: _* )

  require( proof.endSequent.isDefinedAt( Suc( 0 ) ) )
}

/**
 * An NDProof ending with an induction rule:
 * <pre>
 *   (π,,1,,)   (π,,2,,)           (π,,n,,)
 * case 1      case 2     ...     case n
 * -------------------------------------(ind)
 * Γ :- F(t: indTy)
 * </pre>
 *
 * This induction rule can handle inductive data types.
 * The cases are proofs that the various type constructors preserve the formula we want to prove.
 * They are provided via the [[InductionCase]] class.
 *
 * @param cases A sequence of proofs showing that each type constructor preserves the validity of the main formula.
 * @param formula The formula we want to prove via induction.
 */
case class InductionRule( cases: Seq[InductionCase], formula: Abs, term: Expr ) extends CommonRule {
  val Abs( quant @ Var( _, indTy ), qfFormula ) = formula
  require( term.ty == indTy )
  cases foreach { c =>
    require( c.indTy == indTy )
    ( c.hypotheses, c.hypVars ).zipped foreach { ( hyp, eigen ) =>
      require( c.proof.endSequent( hyp ) == Substitution( quant -> eigen )( qfFormula ) )
    }
    require( c.proof.endSequent( Suc( 0 ) ) == Substitution( quant -> c.term )( qfFormula ) )
  }
  require( freeVariables( contexts.flatMap( _.elements ) :+ formula ) intersect
    cases.flatMap( _.eigenVars ).toSet isEmpty )

  val mainFormula = BetaReduction.betaNormalize( formula( term ).asInstanceOf[Formula] )
  override protected def mainFormulaSequent = Sequent() :+ mainFormula
  override def auxIndices: Seq[Seq[SequentIndex]] = cases map { c => c.hypotheses :+ Suc( 0 ) }
  override def immediateSubProofs: Seq[NDProof] = cases map { _.proof }

  private lazy val product = cases.flatMap { _.productIterator } :+ formula :+ term
  override def productArity = product.size
  override def productElement( n: Int ) = product( n )

  override def name = "ind"

  def eigenVariables = cases.flatMap( _.eigenVars ).toSet
}

/**
 * An NDProof ending with excluded middle:
 * <pre>
 *       (π1)       (π2)
 *    Γ, A :- B   Π, ¬A :- B
 *  -------------------------EM
 *          Γ, Π :- B
 * </pre>
 *
 * @param leftSubProof The proof π1.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π2.
 * @param aux2 The index of ¬A.
 */
case class ExcludedMiddleRule( leftSubProof: NDProof, aux1: SequentIndex, rightSubProof: NDProof, aux2: SequentIndex )
  extends BinaryNDProof with CommonRule {

  validateIndices( leftPremise, Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ) )

  val formulaA = leftPremise( aux1 )
  val formulaNegA = rightPremise( aux2 )

  require( Neg( formulaA ) == formulaNegA, s"Formula $formulaNegA is not the negation of $formulaA." )

  val leftB = leftPremise( Suc( 0 ) )
  val rightB = rightPremise( Suc( 0 ) )

  val mainFormula = if ( leftB == rightB ) leftB else
    throw NDRuleCreationException( s"Formula $leftB is not equal to $rightB." )

  override def name = "EM"

  def auxIndices = Seq( Seq( aux1, Suc( 0 ) ), Seq( aux2, Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with a definition
 *
 * <pre>
 *       (π)
 *    Γ :- A[φ]
 *   -----------d
 *    Γ :- A[c]
 * </pre>
 *
 * @param subProof The proof π.
 * @param mainFormula The formula A[c].
 */
case class DefinitionRule( subProof: NDProof, mainFormula: Formula ) extends UnaryNDProof with CommonRule {
  override def name = "d"
  override def auxIndices = Seq( Seq( Suc( 0 ) ) )
  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * Class for reducing boilerplate code in ND companion objects.
 *
 * @param longName The long name of the rule.
 */
class ConvenienceConstructor( val longName: String ) {
  /**
   * Create an NDRuleCreationException with a message starting
   * with "Cannot create longName: ..."
   *
   * @param text The rest of the message.
   * @return
   */
  protected def NDRuleCreationException( text: String ): NDRuleCreationException =
    new NDRuleCreationException( longName, text )

  def findIndicesOrFormulasInPremise( premise: HOLSequent )(
    antIndicesFormulas: Seq[IndexOrFormula], sucIndexFormula: IndexOrFormula ): ( Seq[Formula], Seq[Int], Formula, Int ) = {
    val antReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: antIndicesFormulas ) { ( acc, e ) =>
      e match {
        case IsIndex( Ant( i ) ) => acc + i
        case IsIndex( i: Suc )   => throw NDRuleCreationException( s"Index $i should be in the antecedent." )
        case IsFormula( _ )      => acc
      }
    }

    val ant = for ( e <- antIndicesFormulas ) yield {
      e match {
        case IsIndex( idx @ Ant( i ) ) =>
          antReservedIndices += i
          val f = premise( idx )

          ( f, i )

        case IsFormula( f ) =>
          var i = premise.antecedent.indexOf( f )

          while ( antReservedIndices contains i )
            i = premise.antecedent.indexOf( f, i + 1 )

          if ( i != -1 )
            antReservedIndices += i

          ( f, i )

        case IsIndex( i: Suc ) => throw NDRuleCreationException( s"Index $i should be in the antecedent." )
      }
    }

    val suc = sucIndexFormula match {
      case IsIndex( Suc( i: Int ) ) =>
        ( premise( Suc( i ) ), i )

      case IsFormula( f ) =>
        val i = premise.succedent.indexOf( f )

        ( f, i )

      case IsIndex( i: Ant ) => throw NDRuleCreationException( s"Index $i should be in the succedent." )
    }

    val ( antFormulas, antIndices ) = ant.unzip

    val ( sucFormula, sucIndex ) = suc

    ( antFormulas, antIndices, sucFormula, sucIndex )
  }

  /**
   * Throws an exception if the output of findFormulasInPremise contains any -1 entries.
   *
   * @param premise The sequent in question.
   * @param antFormulas The list of formulas in the antecedent.
   * @param antIndices The list of indices corresponding to antFormulas.
   * @return
   */
  protected def validateIndices( premise: HOLSequent )( antFormulas: Seq[Formula], antIndices: Seq[Int] ) = {
    val antMap = scala.collection.mutable.HashMap.empty[Formula, Int]

    for ( ( f, i ) <- antFormulas zip antIndices ) {
      val count = antMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw NDRuleCreationException( s"Formula $f only found $count times in antecedent of $premise." )

      antMap += f -> ( count + 1 )
    }

  }

  /**
   * Combines findIndicesOrFormulasInPremise and validateIndices. That is, it will return a pair of a lists of indices
   * and an index, and throw an exception if either  list contains a -1.
   *
   * @param premise The sequent in question.
   * @param antIndicesFormulas The list of indices or formulas in the antecedent.
   * @param sucIndexFormula The index or formula in the succedent.
   * @return
   */
  protected def findAndValidate( premise: HOLSequent )(
    antIndicesFormulas: Seq[IndexOrFormula], sucIndexFormula: IndexOrFormula ): ( Seq[Int], Int ) = {
    val ( antFormulas, antIndices, sucFormula, sucIndex ) =
      findIndicesOrFormulasInPremise( premise )( antIndicesFormulas, sucIndexFormula )
    validateIndices( premise )( antFormulas, antIndices )
    ( antIndices, sucIndex )
  }
}

class NDRuleCreationException( name: String, message: String ) extends Exception( s"Cannot create $name: " + message )
