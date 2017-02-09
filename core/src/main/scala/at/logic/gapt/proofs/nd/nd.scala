package at.logic.gapt.proofs.nd

import at.logic.gapt.expr._
import at.logic.gapt.proofs._

import scala.collection.mutable

abstract class NDProof extends SequentProof[HOLFormula, NDProof] {

  def NDRuleCreationException( message: String ): NDRuleCreationException = new NDRuleCreationException( longName, message )

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
 *      Γ :- Δ
 *    ----------
 *     Γ' :- Δ'
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
   * The object connecting the lower and upper sequents.auxFormulas
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
 *    Γ :- Δ   Γ' :- Δ'
 *   ------------------
 *        Π :- Λ
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
 *    Γ1 :- Δ1   Γ2 :- Δ2   Γ3 :- Δ3
 *   --------------------------------
 *               Π :- Λ
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
  def getmiddleSequentConnector: SequentConnector = occConnectors( 1 )

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

trait CommonRule extends NDProof with ContextRule[HOLFormula, NDProof]

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
 *      Γ :- Δ
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
 *       Γ :- Δ
 *     ---------wkn
 *     A, Γ :- Δ
 * </pre>
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningRule( subProof: NDProof, formula: HOLFormula )
    extends UnaryNDProof with CommonRule {
  override def auxIndices = Seq( Seq() )
  override def name = "wkn"
  def mainFormula = formula

  override def mainFormulaSequent = mainFormula +: Sequent()
}

/**
 * An NDProof ending with a contraction:
 * <pre>
 *         (π)
 *     A, A, Γ :- Δ
 *    --------------ctr
 *      A, Γ :- Δ
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionRule( subProof: NDProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryNDProof with CommonRule {

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
   * Convenience constructor for ctr that, given a formula to contract, will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: NDProof, f: HOLFormula ): ContractionRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( Right( f ), Right( f ) ), Left( Suc( 0 ) ) )

    new ContractionRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
  }

}

/**
 * An NDProof consisting of a logical axiom:
 * <pre>
 *    --------ax
 *     A :- A
 * </pre>
 * with A atomic.
 *
 * @param A The atom A.
 */
case class LogicalAxiom( A: HOLFormula ) extends InitialSequent {
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
   * @param A The atom a.
   * @param context The context Γ.
   * @return
   */
  def apply( A: HOLFormula, context: Seq[HOLFormula] ): NDProof = {

    context.foldLeft[NDProof]( LogicalAxiom( A ) ) { ( ant, c ) =>
      WeakeningRule( ant, c )
    }
  }
}

/**
 * An NDProof ending with elimination of the right conjunct
 * <pre>
 *         (π)
 *      Γ :- A ∧ B
 *    --------------
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
    case _                      => throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
  }

  override def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def name = "∧:e1"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with elimination of the left conjunct
 * <pre>
 *         (π)
 *      Γ :- A ∧ B
 *    --------------
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
    case _                       => throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
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
 * --------------------
 *     Γ, Π :- A∧B
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,
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
 *   Γ, A :- C    Δ, B :- C    Π :- A∨B
 * -------------------------------------
 *           Γ, Δ, Π :- C
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param middleSubProof The proof π,,2,,
 * @param aux2 The index of B.
 * @param rightSubProof The proof π,,3,,
 */
case class OrElimRule( leftSubProof: NDProof, aux1: SequentIndex, middleSubProof: NDProof, aux2: SequentIndex, rightSubProof: NDProof )
    extends TernaryNDProof with CommonRule {

  validateIndices( leftPremise, Seq( aux1 ) )
  validateIndices( middlePremise, Seq( aux2 ) )

  val leftDisjunct = leftPremise( aux1 )
  val rightDisjunct = middlePremise( aux2 )

  val disjunction = rightPremise( Suc( 0 ) )

  require( disjunction == Or( leftDisjunct, rightDisjunct ), throw NDRuleCreationException( s"Formula $disjunction is not a disjunction of $leftDisjunct and $rightDisjunct." ) )

  val leftC = leftPremise( Suc( 0 ) )
  val middleC = middlePremise( Suc( 0 ) )

  val mainFormula = if ( leftC == middleC ) leftC else throw NDRuleCreationException( s"Formulas $leftC an $middleC are not the same." )

  def auxIndices = Seq( Seq( aux1, Suc( 0 ) ), Seq( aux2, Suc( 0 ) ), Seq( Suc( 0 ) ) )

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
    val disjunction = rightSubProof.endSequent( Suc( 0 ) )

    val ( leftDisjunct, rightDisjunct ) = disjunction match {
      case Or( f, g ) => ( f, g )
      case _          => throw NDRuleCreationException( s"Formula $disjunction is not a disjunction." )
    }

    val ( leftPremise, middlePremise ) = ( leftSubProof.endSequent, middleSubProof.endSequent )

    val ( leftIndices, _ ) = findAndValidate( leftPremise )( Seq( Right( leftDisjunct ) ), Left( Suc( 0 ) ) )
    val ( middleIndices, _ ) = findAndValidate( middlePremise )( Seq( Right( rightDisjunct ) ), Left( Suc( 0 ) ) )

    new OrElimRule( leftSubProof, Ant( leftIndices( 0 ) ), middleSubProof, Ant( middleIndices( 0 ) ), rightSubProof )
  }
}

/**
 * An NDProof ending with introduction of a disjunction, with a new formula as the right disjunct:
 * <pre>
 *       (π)
 *     Γ :- A
 *    --------------
 *     Γ :- A ∨ B
 * </pre>
 *
 * @param subProof The subproof π.
 * @param rightDisjunct The formula B
 */
case class OrIntro1Rule( subProof: NDProof, rightDisjunct: HOLFormula )
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
 *     Γ :- A
 *    --------------
 *     Γ :- B ∨ A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param leftDisjunct The formula B
 */
case class OrIntro2Rule( subProof: NDProof, leftDisjunct: HOLFormula )
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
 * --------------------------
 *     Γ, Π :- B
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,
 */
case class ImpElimRule( leftSubProof: NDProof, rightSubProof: NDProof )
    extends BinaryNDProof with CommonRule {

  val implication = leftPremise( Suc( 0 ) )
  val antecedent = rightPremise( Suc( 0 ) )

  val mainFormula = implication match {
    case Imp( `antecedent`, consequent ) => consequent
    case Imp( _, _ )                     => throw NDRuleCreationException( s"Proposed main formula $antecedent is not the antecedent of $implication." )
    case _                               => throw NDRuleCreationException( s"Proposed main formula $implication is not an implication." )
  }

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "\u2283:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with introduction of an implication:
 * <pre>
 *         (π)
 *     A, Γ :- B
 *    --------------
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

  override def name = "\u2283:i"

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

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( impPremise ), Left( Suc( 0 ) ) )

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
    else throw NDRuleCreationException( s"Antecedent of $premise doesn't have precisely one element." )
  }
}

/**
 * An NDProof ending with elimination of a negation:
 * <pre>
 *   (π1)      (π2)
 *  Γ :- A    Π :- ¬A
 * -------------------
 *     Γ, Π :- ⊥
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,
 */
case class NegElimRule( leftSubProof: NDProof, rightSubProof: NDProof )
  extends BinaryNDProof with CommonRule {

  val formula= leftPremise( Suc( 0 ) )
  val negatedFormula = rightPremise( Suc( 0 ) )

  val mainFormula = if ( negatedFormula == Neg( formula ) ) Bottom() else throw NDRuleCreationException( s"Formula $negatedFormula is not the negation of $formula." )

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "¬:e"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An NDProof ending with introduction of a negation:
 * <pre>
 *         (π)
 *     A, Γ :- ⊥
 *    -----------
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

  require( bottom  == Bottom(), s"Formula $bottom is not ⊥." )

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

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( negation ), Left( Suc( 0 ) ) )

    new NegIntroRule( subProof, Ant( antIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for ¬:i
   * If the subproof has precisely one element in the antecedent of its premise, this element will be the aux index.
   *
   * @param subProof The subproof.
   * @return
   */
  def apply( subProof: NDProof ): NegIntroRule = {
    val premise = subProof.endSequent

    if ( premise.antecedent.size == 1 ) apply( subProof, Ant( 0 ) )
    else throw NDRuleCreationException( s"Antecedent of $premise doesn't have precisely one element." )
  }
}

/**
 * An NDProof eliminating ⊥ :
 * <pre>
 *       (π)
 *     Γ :- ⊥
 *     --------
 *     Γ :- A
 * </pre>
 *
 * @param subProof The subproof π.
 * @param mainFormula The formula A.
 */
case class BottomElimRule( subProof: NDProof, mainFormula: HOLFormula )
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
    throw NDRuleCreationException( s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = ${BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) )}, but is $auxFormula." )

  def mainFormula = BetaReduction.betaNormalize( All( quantifiedVariable, subFormula ) )

  override def name = "∀:i"

  def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallIntroRule extends ConvenienceConstructor( "ForallIntroRule" ) {

  /**
   * Convenience constructor for ∀:i that, given a main formula and an eigenvariable, will try to construct an inference with that instantiation.
   *
   * @param subProof      The subproof.
   * @param mainFormula   The formula to be inferred. Must be of the form ∀x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: NDProof, mainFormula: HOLFormula, eigenVariable: Var ): ForallIntroRule = mainFormula match {
    case All( v, subFormula ) =>
      val auxFormula = Substitution( v, eigenVariable )( subFormula )

      val premise = subProof.endSequent

      val ( _, indices ) = findAndValidate( premise )( Seq(), Right( auxFormula ) )

      ForallIntroRule( subProof, eigenVariable, v )

    case _ => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }
}

/**
 * An NDProof ending with a universal quantifier elimination:
 * <pre>
 *        (π)
 *      Γ :- ∀x.A
 *     -------------∀:l
 *      Γ :- A[x\t]
 * </pre>
 *
 * @param subProof The proof π.
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ForallElimRule( subProof: NDProof, A: HOLFormula, term: LambdaExpression, v: Var )
    extends UnaryNDProof with CommonRule {

  val mainFormula = Substitution( v, term )( A )

  override def name = "∀:l"

  def auxIndices = Seq( Seq( Suc( 0 ) ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallElimRule extends ConvenienceConstructor( "ForallElimRule" ) {
  /**
   * Convenience constructor for ∀:l that, given a term, will try to construct an inference with that instantiation.
   *
   * @param subProof    The subproof.
   * @param term        A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: NDProof, term: LambdaExpression ): ForallElimRule = {
    val premise = subProof.endSequent

    val universal = premise( Suc( 0 ) )

    universal match {
      case All( v, subFormula ) => ForallElimRule( subProof, subFormula, term, v )
      case _                    => throw NDRuleCreationException( s"Proposed main formula $universal is not universally quantified." )
    }
  }
}

/**
 * An NDProof ending with induction:
 * <pre>
 *    (π1)         (π2)
 *   Γ :- A(0)    Π :- ∀α.A(α) → A(s(α))
 * ---------------------------------------ind
 *               Γ, Π :- A(t)
 * </pre>
 *
 * @param leftSubProof The proof π,,1,,.
 * @param rightSubProof The proof π,,2,,
 */
case class InductionRule( leftSubProof: NDProof, rightSubProof: NDProof, term: LambdaExpression )
    extends BinaryNDProof with CommonRule {

  val baseCase = leftPremise( Suc( 0 ) )
  val stepCase = rightPremise( Suc( 0 ) )

  val ( v, a ) = stepCase match {
    case All( v, Imp( a1, a2 ) ) if Substitution( v, le"s $v" )( a1 ) == a2 => ( v, a1 )
    case _ => throw NDRuleCreationException( s"Formula $stepCase is not of the form ∀α.A(α) → A(s(α))." )
  }

  require( Substitution( v, le"0" )( a ) == baseCase, throw NDRuleCreationException( s"Formula $baseCase is not of the form A(0)." ) )

  val mainFormula = Substitution( v, term )( a )

  def auxIndices = Seq( Seq( Suc( 0 ) ), Seq( Suc( 0 ) ) )

  override def name = "ind"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * Class for reducing boilerplate code in ND companion objects.
 *
 * @param longName The long name of the rule.
 */
class ConvenienceConstructor( val longName: String ) {
  type IndexOrFormula = Either[SequentIndex, HOLFormula]

  /**
   * Create an NDRuleCreationException with a message starting with "Cannot create $longName: ..."
   *
   * @param text The rest of the message.
   * @return
   */
  protected def NDRuleCreationException( text: String ): NDRuleCreationException = new NDRuleCreationException( longName, text )

  def findIndicesOrFormulasInPremise( premise: HOLSequent )( antIndicesFormulas: Seq[IndexOrFormula], sucIndexFormula: IndexOrFormula ): ( Seq[HOLFormula], Seq[Int], HOLFormula, Int ) = {
    val antReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: antIndicesFormulas ) { ( acc, e ) =>
      e match {
        case Left( Ant( i ) ) => acc + i
        case Left( i: Suc )   => throw NDRuleCreationException( s"Index $i should be in the antecedent." )
        case Right( _ )       => acc
      }
    }

    val ant = for ( e <- antIndicesFormulas ) yield {
      e match {
        case Left( idx @ Ant( i ) ) =>
          antReservedIndices += i
          val f = premise( idx )

          ( f, i )

        case Right( f: HOLFormula ) =>
          var i = premise.antecedent.indexOf( f )

          while ( antReservedIndices contains i )
            i = premise.antecedent.indexOf( f, i + 1 )

          if ( i != -1 )
            antReservedIndices += i

          ( f, i )

        case Left( i: Suc ) => throw NDRuleCreationException( s"Index $i should be in the antecedent." )
      }
    }

    val suc = sucIndexFormula match {
      case Left( Suc( i: Int ) ) =>
        ( premise( Suc( i ) ), i )

      case Right( f: HOLFormula ) =>
        val i = premise.succedent.indexOf( f )

        ( f, i )

      case Left( i: Ant ) => throw NDRuleCreationException( s"Index $i should be in the succedent." )
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
  protected def validateIndices( premise: HOLSequent )( antFormulas: Seq[HOLFormula], antIndices: Seq[Int] ) = {
    val antMap = scala.collection.mutable.HashMap.empty[HOLFormula, Int]

    for ( ( f, i ) <- antFormulas zip antIndices ) {
      val count = antMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw NDRuleCreationException( s"Formula $f only found $count times in antecedent of $premise." )

      antMap += f -> ( count + 1 )
    }

  }

  /**
   * Combines findIndicesOrFormulasInPremise and validateIndices. That is, it will return a pair of lists of indices and throw an exception if either
   * list contains a -1.
   *
   * @param premise The sequent in question.
   * @param antIndicesFormulas The list of indices or formulas in the antecedent.
   * @param sucIndexFormula The list of indices or formulas in the succedent.
   * @return
   */
  protected def findAndValidate( premise: HOLSequent )( antIndicesFormulas: Seq[IndexOrFormula], sucIndexFormula: IndexOrFormula ): ( Seq[Int], Int ) = {
    val ( antFormulas, antIndices, sucFormula, sucIndex ) = findIndicesOrFormulasInPremise( premise )( antIndicesFormulas, sucIndexFormula )
    validateIndices( premise )( antFormulas, antIndices )
    ( antIndices, sucIndex )
  }
}

class NDRuleCreationException( name: String, message: String ) extends Exception( s"Cannot create $name: " + message )