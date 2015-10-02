package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLSubstitution, FOLMatchingAlgorithm }
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._

import scala.collection.mutable

abstract class LKProof extends SequentProof[HOLFormula, LKProof] {

  def LKRuleCreationException( message: String ): LKRuleCreationException = new LKRuleCreationException( longName, message )

  /**
   * The end-sequent of the rule.
   */
  def endSequent: HOLSequent

  override def conclusion = endSequent

  /**
   * Checks whether indices are in the right place and premise is defined at all of them.
   *
   * @param premise The sequent to be checked.
   * @param antecedentIndices Indices that should be in the antecedent.
   * @param succedentIndices Indices that should be in the succedent.
   */
  protected def validateIndices( premise: HOLSequent, antecedentIndices: Seq[SequentIndex], succedentIndices: Seq[SequentIndex] ): Unit = {
    val antSet = mutable.HashSet[SequentIndex]()
    val sucSet = mutable.HashSet[SequentIndex]()

    for ( i <- antecedentIndices ) i match {
      case Ant( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw LKRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( antSet contains i )
          throw LKRuleCreationException( s"Duplicate index $i for sequent $premise." )

        antSet += i

      case Suc( _ ) => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
    }

    for ( i <- succedentIndices ) i match {
      case Suc( _ ) =>

        if ( !premise.isDefinedAt( i ) )
          throw LKRuleCreationException( s"Sequent $premise is not defined at index $i." )

        if ( sucSet contains i )
          throw LKRuleCreationException( s"Duplicate index $i for sequent $premise." )

        sucSet += i

      case Ant( _ ) => throw LKRuleCreationException( s"Index $i should be in the succedent." )
    }
  }
}

/**
 * An LKProof deriving a sequent from another sequent:
 * <pre>
 *        (π)
 *      Γ :- Δ
 *    ----------
 *     Γ' :- Δ'
 * </pre>
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
  def getOccConnector: OccConnector = occConnectors.head

  /**
   * The upper sequent of the rule.
   *
   * @return
   */
  def premise = subProof.endSequent

  override def immediateSubProofs = Seq( subProof )
}

object UnaryLKProof {
  def unapply( p: UnaryLKProof ) = Some( p.endSequent, p.subProof )
}

/**
 * An LKProof deriving a sequent from two other sequents:
 * <pre>
 *     (π1)     (π2)
 *    Γ :- Δ   Γ' :- Δ'
 *   ------------------
 *        Π :- Λ
 * </pre>
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
  def getLeftOccConnector: OccConnector = occConnectors.head

  /**
   * The object connecting the lower and right upper sequents.
   *
   * @return
   */
  def getRightOccConnector: OccConnector = occConnectors.tail.head

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

object BinaryLKProof {
  def unapply( p: BinaryLKProof ) = Some( p.endSequent, p.leftSubProof, p.rightSubProof )
}

trait CommonRule extends LKProof {

  private def concat[A]( sequents: Seq[Sequent[A]] ) = sequents match {
    case Seq() => Sequent()
    case _     => sequents.reduce( _ ++ _ )
  }

  protected def formulasToBeDeleted = auxIndices

  protected def mainFormulaSequent: HOLSequent

  protected def contexts = for ( ( p, is ) <- premises zip formulasToBeDeleted ) yield p.delete( is )

  override def endSequent = mainFormulaSequent.antecedent ++: concat( contexts ) :++ mainFormulaSequent.succedent

  override def mainIndices = ( mainFormulaSequent.antecedent.map( _ => true ) ++: concat( contexts ).map( _ => false ) :++ mainFormulaSequent.succedent.map( _ => true ) ).indicesWhere( _ == true )

  private val contextIndices = for ( ( p, is ) <- premises zip formulasToBeDeleted ) yield p.indicesSequent.delete( is )

  override def occConnectors = for ( i <- contextIndices.indices ) yield {
    val ( leftContexts, currentContext, rightContext ) = ( contextIndices.take( i ), contextIndices( i ), contextIndices.drop( i + 1 ) )
    val leftContextIndices = leftContexts.map( c => c.map( _ => Seq() ) )
    val currentContextIndices = currentContext.map( i => Seq( i ) )
    val rightContextIndices = rightContext.map( c => c.map( _ => Seq() ) )
    val auxIndicesAntecedent = mainFormulaSequent.antecedent.map( _ => formulasToBeDeleted( i ) )
    val auxIndicesSuccedent = mainFormulaSequent.succedent.map( _ => formulasToBeDeleted( i ) )
    new OccConnector( endSequent, premises( i ),
      auxIndicesAntecedent ++: ( concat( leftContextIndices ) ++ currentContextIndices ++ concat( rightContextIndices ) ) :++ auxIndicesSuccedent )
  }
}

/**
 * An LKProof consisting of a single sequent:
 * <pre>
 *     --------ax
 *      Γ :- Δ
 * </pre>
 */
abstract class InitialSequent extends LKProof {

  override def name = "ax"

  override def mainIndices = endSequent.indices

  override def auxIndices = Seq()

  override def immediateSubProofs = Seq()

  override def occConnectors = Seq()
}

object InitialSequent {
  def unapply( proof: InitialSequent ) = Some( proof.endSequent )
}

case class ArbitraryAxiom( endSequent: Sequent[HOLAtom] ) extends InitialSequent

/**
 * An LKProof introducing ⊤ on the right:
 * <pre>
 *       --------⊤:r
 *         :- ⊤
 * </pre>
 */
case object TopAxiom extends InitialSequent {
  override def name: String = "⊤:r"
  override def endSequent = HOLSequent( Nil, Seq( Top() ) )
  def mainFormula = Top()
}

/**
 * An LKProof introducing ⊥ on the left:
 * <pre>
 *       --------⊥:l
 *         ⊥ :-
 * </pre>
 */
case object BottomAxiom extends InitialSequent {
  override def name: String = "⊥:l"
  override def endSequent = HOLSequent( Seq( Bottom() ), Nil )
  def mainFormula = Top()
}

/**
 * An LKProof consisting of a logical axiom:
 * <pre>
 *    --------ax
 *     A :- A
 * </pre>
 * with A atomic.
 *
 * @param A The atom A.
 */
case class LogicalAxiom( A: HOLAtom ) extends InitialSequent {
  override def endSequent = HOLSequent( Seq( A ), Seq( A ) )
  def mainFormula = A
}

/**
 * An LKProof consisting of a reflexivity axiom:
 * <pre>
 *    ------------ax
 *      :- s = s
 * </pre>
 * with s a term.
 *
 * @param s The term s.
 */
case class ReflexivityAxiom( s: LambdaExpression ) extends InitialSequent {
  override def endSequent = HOLSequent( Seq(), Seq( Eq( s, s ) ) )
  def mainFormula = Eq( s, s )
}

object Axiom {
  def apply( sequent: HOLSequent ): InitialSequent = sequent match {
    case Sequent( Seq( f: HOLAtom ), Seq( g: HOLAtom ) ) if f == g => LogicalAxiom( f )
    case Sequent( Seq(), Seq( Top() ) ) => TopAxiom
    case Sequent( Seq( Bottom() ), Seq() ) => BottomAxiom
    case Sequent( Seq(), Seq( Eq( s: LambdaExpression, t: LambdaExpression ) ) ) if s == t => ReflexivityAxiom( s )
    case _ if sequent.forall( _.isInstanceOf[HOLAtom] ) => ArbitraryAxiom( sequent.asInstanceOf[Sequent[HOLAtom]] )

    case _ => throw new IllegalArgumentException( s"Cannot create axiom from sequent $sequent." )
  }

  def apply( ant: Seq[HOLFormula], suc: Seq[HOLFormula] ): InitialSequent = apply( Sequent( ant, suc ) )
}

/**
 * An LKProof ending with a left contraction:
 * <pre>
 *         (π)
 *     A, A, Γ :- Δ
 *    --------------
 *      A, Γ :- Δ
 * </pre>
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliar formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  val mainFormula = premise( aux1 )

  override def name = "c:l"

  override def mainFormulaSequent = mainFormula +: Sequent()

}

object ContractionLeftRule extends RuleConvenienceObject( "ContractionLeftRule" ) {
  /**
   * Convenience constructor for c:l that, given a formula to contract on the left, will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: HOLFormula ): ContractionLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( f, f ), Seq() )

    new ContractionLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
  }

}

/**
 * An LKProof ending with a right contraction:
 * <pre>
 *         (π)
 *     Γ :- Δ, A, A
 *    --------------
 *      Γ :- Δ, A
 * </pre>
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux1, aux2 ) )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliar formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  val mainFormula = premise( aux1 )

  override def name = "c:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula

}

object ContractionRightRule extends RuleConvenienceObject( "ContractionRightRule" ) {
  /**
   * Convenience constructor for c:r that, given a formula to contract on the right, will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: HOLFormula ): ContractionRightRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( f, f ) )
    new ContractionRightRule( subProof, Suc( indices( 0 ) ), Suc( indices( 1 ) ) )
  }

}

/**
 * An LKProof ending with a left weakening:
 * <pre>
 *        (π)
 *       Γ :- Δ
 *     ---------w:l
 *     A, Γ :- Δ
 * </pre>
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningLeftRule( subProof: LKProof, formula: HOLFormula ) extends UnaryLKProof with CommonRule {
  override def auxIndices = Seq( Seq() )
  override def name = "w:l"
  def mainFormula = formula

  override def mainFormulaSequent = mainFormula +: Sequent()
}

/**
 * An LKProof ending with a right weakening:
 * <pre>
 *        (π)
 *       Γ :- Δ
 *     ---------w:r
 *     Γ :- Δ, A
 * </pre>
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningRightRule( subProof: LKProof, formula: HOLFormula ) extends UnaryLKProof with CommonRule {
  override def auxIndices = Seq( Seq() )
  override def name = "w:r"
  def mainFormula = formula

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

/**
 * An LKProof ending with a cut:
 * <pre>
 *      (π1)         (π2)
 *    Γ :- Δ, A   A, Π :- Λ
 *   ------------------------
 *        Γ, Π :- Δ, Λ
 * </pre>
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A in π,,1,,.
 * @param rightSubProof The proof π,,2,,.
 * @param aux2 The index of A in π,,2,,.
 */
case class CutRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  if ( leftPremise( aux1 ) != rightPremise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliar formulas are not the same." )

  override def name = "cut"

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def mainFormulaSequent = Sequent()
}

object CutRule extends RuleConvenienceObject( "CutRule" ) {
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

    val ( _, sucIndices ) = findAndValidate( leftPremise )( Seq(), Seq( A ) )
    val ( antIndices, _ ) = findAndValidate( rightPremise )( Seq( A ), Seq() )

    new CutRule( leftSubProof, Suc( sucIndices( 0 ) ), rightSubProof, Ant( antIndices( 0 ) ) )
  }
}

/**
 * An LKProof ending with a negation on the left:
 * <pre>
 *       (π)
 *    Γ :- Δ, A
 *   -----------¬:l
 *   ¬A, Γ :- Δ
 * </pre>
 * @param subProof The proof π.
 * @param aux The index of A in the succedent.
 */
case class NegLeftRule( subProof: LKProof, aux: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  val mainFormula = Neg( premise( aux ) )

  override def auxIndices = Seq( Seq( aux ) )
  override def name = "¬:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object NegLeftRule extends RuleConvenienceObject( "NegLeftRule" ) {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof
   * @param formula
   * @return
   */
  def apply( subProof: LKProof, formula: HOLFormula ): NegLeftRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( formula ) )

    new NegLeftRule( subProof, Suc( indices( 0 ) ) )
  }
}

/**
 * An LKProof ending with a negation on the right:
 * <pre>
 *       (π)
 *    A, Γ :- Δ
 *   -----------¬:r
 *   Γ :- Δ, ¬A
 * </pre>
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 */
case class NegRightRule( subProof: LKProof, aux: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  val mainFormula = Neg( premise( aux ) )

  override def auxIndices = Seq( Seq( aux ) )
  override def name = "¬:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object NegRightRule extends RuleConvenienceObject( "NegRightRule" ) {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof
   * @param formula
   * @return
   */
  def apply( subProof: LKProof, formula: HOLFormula ): NegRightRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( formula ), Seq() )

    new NegRightRule( subProof, Ant( indices( 0 ) ) )
  }
}

/**
 * An LKProof ending with a conjunction on the left:
 * <pre>
 *         (π)
 *     A, B, Γ :- Δ
 *    --------------
 *    A ∧ B, Γ :- Δ
 * </pre>
 * @param subProof The subproof π.
 * @param aux1 The index of A.//<editor-fold desc="Base proof classes">
 * @param aux2 The index of B.
 */
case class AndLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  val leftConjunct = premise( aux1 )
  val rightConjunct = premise( aux2 )
  val mainFormula = And( leftConjunct, rightConjunct )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∧:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object AndLeftRule extends RuleConvenienceObject( "AndLeftRule" ) {
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

    val ( indices, _ ) = findAndValidate( premise )( Seq( A, B ), Seq() )

    new AndLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
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
    case _           => throw LKRuleCreationException( s"Proposed main formula $F is not a conjunction." )
  }
}

/**
 * An LKProof ending with a conjunction on the right:
 * <pre>
 *    (π1)         (π2)
 *   Γ :- Δ, A    Π :- Λ, B
 * --------------------------
 *     Γ, Π :- Δ, Λ, A∧B
 * </pre>
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class AndRightRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq(), Seq( aux2 ) )

  val leftConjunct = leftPremise( aux1 )
  val rightConjunct = rightPremise( aux2 )

  val mainFormula = And( leftConjunct, rightConjunct )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "∧:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object AndRightRule extends RuleConvenienceObject( "AndRightRule" ) {
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

    val ( _, leftIndices ) = findAndValidate( leftPremise )( Seq(), Seq( A ) )
    val ( _, rightIndices ) = findAndValidate( rightPremise )( Seq(), Seq( B ) )

    new AndRightRule( leftSubProof, Suc( leftIndices( 0 ) ), rightSubProof, Suc( rightIndices( 0 ) ) )
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
    case _           => throw LKRuleCreationException( s"Proposed main formula $F is not a conjunction." )
  }
}

/**
 * An LKProof ending with a disjunction on the left:
 * <pre>
 *     (π1)         (π2)
 *   A, Γ :- Δ    B, Π :- Λ
 * --------------------------
 *     A∨B, Γ, Π :- Δ, Λ
 * </pre>
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class OrLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq( aux1 ), Seq() )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  val leftDisjunct = leftPremise( aux1 )
  val rightDisjunct = rightPremise( aux2 )

  val mainFormula = Or( leftDisjunct, rightDisjunct )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "∨:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object OrLeftRule extends RuleConvenienceObject( "OrLeftRule" ) {
  /**
   * Convenience constructor for ∨:l that, given formulas on the left, will automatically pick their respective first occurrences.
   *
   * @param leftSubProof
   * @param A
   * @param rightSubProof
   * @param B
   * @return
   */
  def apply( leftSubProof: LKProof, A: HOLFormula, rightSubProof: LKProof, B: HOLFormula ): OrLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( leftIndices, _ ) = findAndValidate( leftPremise )( Seq( A ), Seq() )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( B ), Seq() )

    new OrLeftRule( leftSubProof, Ant( leftIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
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
    case _          => throw LKRuleCreationException( s"Proposed main formula $F is not a disjunction." )
  }
}

/**
 * An LKProof ending with a disjunction on the right:
 * <pre>
 *         (π)
 *     Γ :- Δ, A, B
 *    --------------
 *     Γ :- Δ, A ∨ B
 * </pre>
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class OrRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux1, aux2 ) )

  val leftDisjunct = premise( aux1 )
  val rightDisjunct = premise( aux2 )
  val mainFormula = Or( leftDisjunct, rightDisjunct )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∨:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object OrRightRule extends RuleConvenienceObject( "OrRightRule" ) {
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

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( A, B ) )

    new OrRightRule( subProof, Suc( indices( 0 ) ), Suc( indices( 1 ) ) )
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
    case _          => throw LKRuleCreationException( s"Proposed main formula $F is not a disjunction." )
  }
}

/**
 * An LKProof ending with an implication on the left:
 * <pre>
 *     (π1)         (π2)
 *   Γ :- Δ, A    B, Π :- Λ
 * --------------------------
 *     A→B, Γ, Π :- Δ, Λ
 * </pre>
 * @param leftSubProof The proof π,,1,,.
 * @param aux1 The index of A.
 * @param rightSubProof The proof π,,2,,
 * @param aux2 The index of B.
 */
case class ImpLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex ) extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  val impPremise = leftPremise( aux1 )
  val impConclusion = rightPremise( aux2 )

  val mainFormula = Imp( impPremise, impConclusion )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "\u2283:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ImpLeftRule extends RuleConvenienceObject( "ImpLeftRule" ) {
  /**
   * Convenience constructor for →:l that, given aux formulas, will automatically pick their respective first occurrences.
   *
   * @param leftSubProof
   * @param A
   * @param rightSubProof
   * @param B
   * @return
   */
  def apply( leftSubProof: LKProof, A: HOLFormula, rightSubProof: LKProof, B: HOLFormula ): ImpLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, leftIndices ) = findAndValidate( leftPremise )( Seq(), Seq( A ) )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( B ), Seq() )

    new ImpLeftRule( leftSubProof, Suc( leftIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:l that, given a proposed main formula A → B, will attempt to create an inference with this main formula.
   *
   * @param leftSubProof
   * @param rightSubProof
   * @param F
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, F: HOLFormula ): ImpLeftRule = F match {
    case Imp( f, g ) => apply( leftSubProof, f, rightSubProof, g )
    case _           => throw LKRuleCreationException( s"Proposed main formula $F is not a implication." )
  }
}

/**
 * An LKProof ending with an implication on the right:
 * <pre>
 *         (π)
 *     A, Γ :- Δ, B
 *    --------------
 *     Γ :- Δ, A → B
 * </pre>
 * @param subProof The subproof π.
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class ImpRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1 ), Seq( aux2 ) )

  val impPremise = premise( aux1 )
  val impConclusion = premise( aux2 )
  val mainFormula = Imp( impPremise, impConclusion )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "\u2283:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ImpRightRule extends RuleConvenienceObject( "ImpRightRule" ) {
  /**
   * Convenience constructor for →:r that, given two aux formulas, will automatically pick the respective first instances of these formulas.
   *
   * @param subProof
   * @param A
   * @param B
   * @return
   */
  def apply( subProof: LKProof, A: HOLFormula, B: HOLFormula ): ImpRightRule = {
    val premise = subProof.endSequent

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( A ), Seq( B ) )

    new ImpRightRule( subProof, Ant( antIndices( 0 ) ), Suc( sucIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:r that, given a proposed main formula A → B, will attempt to create an inference with this main formula.
   *
   * @param subProof
   * @param F
   * @return
   */
  def apply( subProof: LKProof, F: HOLFormula ): ImpRightRule = F match {
    case Imp( f, g ) => apply( subProof, f, g )
    case _           => throw LKRuleCreationException( s"Proposed main formula $F is not an implication." )
  }
}

/**
 * An LKProof ending with a universal quantifier on the left:
 * <pre>
 *            (π)
 *      A[x\t], Γ :- Δ
 *     ----------------∀:l
 *       ∀x.A, Γ :- Δ
 * </pre>
 * @param subProof The proof π.
 * @param aux The index of A[x\t].
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ForallLeftRule( subProof: LKProof, aux: SequentIndex, A: HOLFormula, term: LambdaExpression, v: Var ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  if ( premise( aux ) != Substitution( v, term )( A ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula = All( v, A )

  override def name = "∀:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ForallLeftRule extends RuleConvenienceObject( "ForallLeftRule" ) {
  /**
   * Convenience constructor for ∀:l that, a main formula and a term, will try to construct an inference with these formulas.
   *
   * @param subProof
   * @param mainFormula
   * @param term
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula, term: LambdaExpression ): ForallLeftRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = Substitution( v, term )( subFormula )
        val i = premise.antecedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in antecedent of $premise." )

        ForallLeftRule( subProof, Ant( i ), subFormula, term, v )

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
    }
  }

  def apply( subProof: LKProof, mainFormula: HOLFormula ): ForallLeftRule = mainFormula match {
    case All( v, subFormula ) => apply( subProof, mainFormula, v )

    case _                    => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }
}

/**
 * An LKProof ending with a universal quantifier on the right:
 * <pre>
 *           (π)
 *      Γ :- Δ, A[x\α]
 *     ---------------∀:r
 *      Γ :- Δ, ∀x.A
 * </pre>
 * This rule is only applicable if the eigenvariable condition is satisfied: α must not occur freely in Γ :- Δ.
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\α].
 * @param eigenVariable The variable α.
 * @param quantifiedVariable The variable x.
 */
case class ForallRightRule( subProof: LKProof, aux: SequentIndex, eigenVariable: Var, quantifiedVariable: Var ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  val ( auxFormula, context ) = premise focus aux

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw LKRuleCreationException( s"Eigenvariable condition is violated." )

  val mainFormula = All( quantifiedVariable, Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  override def name = "∀:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallRightRule extends RuleConvenienceObject( "ForallRightRule" ) {
  def apply( subProof: LKProof, mainFormula: HOLFormula, eigenVariable: Var ): ForallRightRule = mainFormula match {
    case All( v, subFormula ) =>
      val auxFormula = Substitution( v, eigenVariable )( subFormula )

      val premise = subProof.endSequent

      val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

      ForallRightRule( subProof, Suc( indices( 0 ) ), eigenVariable, v )

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }

  def apply( subProof: LKProof, mainFormula: HOLFormula ): ForallRightRule = mainFormula match {
    case All( v, subFormula ) => apply( subProof, mainFormula, v )

    case _                    => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }
}

/**
 * An LKProof ending with an existential quantifier on the left:
 * <pre>
 *           (π)
 *      A[x\α], Γ :- Δ
 *     ---------------∀:r
 *       ∃x.A Γ :- Δ
 * </pre>
 * This rule is only applicable if the eigenvariable condition is satisfied: α must not occur freely in Γ :- Δ.
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\α].
 * @param eigenVariable The variable α.
 * @param quantifiedVariable The variable x.
 */
case class ExistsLeftRule( subProof: LKProof, aux: SequentIndex, eigenVariable: Var, quantifiedVariable: Var ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  val ( auxFormula, context ) = premise focus aux

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw LKRuleCreationException( s"Eigenvariable condition is violated." )

  val mainFormula = Ex( quantifiedVariable, Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  override def name = "∃:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ExistsLeftRule extends RuleConvenienceObject( "ExistsLeftRule" ) {
  def apply( subProof: LKProof, mainFormula: HOLFormula, eigenVariable: Var ): ExistsLeftRule = mainFormula match {
    case Ex( v, subFormula ) =>
      val auxFormula = Substitution( v, eigenVariable )( subFormula )

      val premise = subProof.endSequent

      val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Seq() )
      ExistsLeftRule( subProof, Ant( indices( 0 ) ), eigenVariable, v )

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }

  def apply( subProof: LKProof, mainFormula: HOLFormula ): ExistsLeftRule = mainFormula match {
    case Ex( v, subFormula ) => apply( subProof, mainFormula, v )

    case _                   => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }
}

/**
 * An LKProof ending with an existential quantifier on the right:
 * <pre>
 *            (π)
 *      Γ :- Δ, A[x\t]
 *     ----------------∃:r
 *       Γ :- Δ, ∃x.A
 * </pre>
 * @param subProof The proof π.
 * @param aux The index of A[x\t].
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ExistsRightRule( subProof: LKProof, aux: SequentIndex, A: HOLFormula, term: LambdaExpression, v: Var ) extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  if ( premise( aux ) != Substitution( v, term )( A ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula = Ex( v, A )

  override def name = "∃:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ExistsRightRule extends RuleConvenienceObject( "ExistsRightRule" ) {
  /**
   * Convenience constructor for ∃:r that, a main formula and a term, will try to construct an inference with these formulas.
   *
   * @param subProof
   * @param mainFormula
   * @param term
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula, term: LambdaExpression ): ExistsRightRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case Ex( v, subFormula ) =>
        val auxFormula = Substitution( v, term )( subFormula )
        val i = premise.succedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in antecedent of $premise." )

        ExistsRightRule( subProof, Suc( i ), subFormula, term, v )

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
    }
  }

  def apply( subProof: LKProof, mainFormula: HOLFormula ): ExistsRightRule = mainFormula match {
    case Ex( v, subFormula ) => apply( subProof, mainFormula, v )

    case _                   => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }
}

object WeakQuantifierRule {
  def unapply( p: LKProof ) = p match {
    case ForallLeftRule( subProof, aux, f, t, v ) =>
      Some( ( subProof, aux, f, t, v, false ) )
    case ExistsRightRule( subProof, aux, f, t, v ) =>
      Some( ( subProof, aux, f, t, v, true ) )
    case _ => None
  }
}

object StrongQuantifierRule {
  def unapply( p: LKProof ) = p match {
    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      Some( ( subProof, aux, eigen, quant, false ) )
    case ForallRightRule( subProof, aux, eigen, quant ) =>
      Some( ( subProof, aux, eigen, quant, true ) )
    case _ => None
  }
}

/**
 * Abstract class that performs most of the construction of left and right equality rules.
 *
 * @param subProof
 * @param eq
 * @param aux
 * @param pos
 */
abstract class EqualityRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, pos: HOLPosition ) extends UnaryLKProof with CommonRule {

  aux match {
    case Ant( _ ) => validateIndices( premise, Seq( eq, aux ), Seq() )
    case Suc( _ ) => validateIndices( premise, Seq( eq ), Seq( aux ) )
  }

  val equation = premise( eq )

  val auxFormula = premise( aux )

  val mainFormula = equation match {
    case Eq( s, t ) =>
      auxFormula( pos ) match {
        case `s` =>
          auxFormula.replace( pos, t )
        case `t` =>
          auxFormula.replace( pos, s )
        case _ =>
          throw LKRuleCreationException( s"Position $pos in $auxFormula should be $s or $t, but is ${auxFormula( pos )}." )
      }

    case _ => throw LKRuleCreationException( s"Formula $equation is not an equation." )
  }

  def auxIndices = Seq( Seq( eq, aux ) )

  override def formulasToBeDeleted = Seq( Seq( aux ) )

}

/**
 * An LKProof ending with a left equality rule.
 * There are two possible cases according to which direction the rule is applied in:
 *
 * <pre>
 *            (π)                            (π)
 *    A[s], s = t, Γ :- Δ            A[t], s = t, Γ :- Δ
 *   ---------------------eq:l      ---------------------eq:l
 *    A[t], s = t, Γ :- Δ            A[s], s = t, Γ :- Δ
 *
 * </pre>
 *
 * In either case, the rule only replaces a single term occurrence. The position of this occurrence is given by the pos argument.
 *
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param pos The position of the term to be replaced within A. FIXME: I think it would be convenient to allow FOLPositions here.
 */
case class EqualityLeftRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, pos: HOLPosition ) extends EqualityRule( subProof, eq, aux, pos ) {

  validateIndices( premise, Seq( eq, aux ), Seq() )

  override def name = "eq:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object EqualityLeftRule extends RuleConvenienceObject( "EqualityLeftRule" ) {
  def apply( subProof: LKProof, eqFormula: HOLFormula, auxFormula: HOLFormula, main: HOLFormula ): EqualityLeftRule = eqFormula match {
    case Eq( s, t ) =>
      val premise = subProof.endSequent

      val ( indices, _ ) = findAndValidate( premise )( Seq( eqFormula, auxFormula ), Seq() )

      if ( s == t && auxFormula == main ) {
        val sAux = auxFormula.find( s )

        if ( sAux.isEmpty )
          throw LKRuleCreationException( "Eq is trivial, but term " + s + " does not occur in " + auxFormula + "." )

        EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), sAux.head )

      } else if ( s == t && auxFormula != main ) {
        throw LKRuleCreationException( "Eq is trivial, but aux formula " + auxFormula + " and main formula " + main + "differ." )

      } else if ( s != t && auxFormula == main ) {
        throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

      } else {
        val sAux = auxFormula.find( s )
        val sMain = main.find( s )

        val tAux = auxFormula.find( t )
        val tMain = main.find( t )

        if ( sAux.isEmpty && tAux.isEmpty )
          throw LKRuleCreationException( "Neither " + s + " nor " + t + " found in formula " + auxFormula + "." )

        val tToS = sMain intersect tAux
        val sToT = tMain intersect sAux

        if ( sToT.length == 1 && tToS.isEmpty ) {
          val p = sToT.head
          val mainNew = HOLPosition.replace( auxFormula, p, t )
          if ( mainNew == main ) {
            EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), p )
          } else throw LKRuleCreationException( "Replacement (" + auxFormula + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + "." )
        } else if ( tToS.length == 1 && sToT.isEmpty ) {
          val p = tToS.head
          val mainNew = HOLPosition.replace( auxFormula, p, s )
          if ( mainNew == main ) {
            EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), p )
          } else throw LKRuleCreationException( "Replacement (" + auxFormula + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + "." )
        } else throw LKRuleCreationException( "Formulas " + auxFormula + " and " + main + " don't differ in exactly one position." )
      }

    case _ => throw LKRuleCreationException( s"Formula $eqFormula is not an equation." )
  }
}

/**
 * An LKProof ending with a right equality rule.
 * There are two possible cases according to which direction the rule is applied in:
 *
 * <pre>
 *            (π)                            (π)
 *    s = t, Γ :- Δ, A[s]            s = t, Γ :- Δ, A[t]
 *   ---------------------eq:r      ---------------------eq:r
 *    s = t, Γ :- Δ, A[t]            s = t, Γ :- Δ, A[s]
 * </pre>
 *
 * In either case, the rule only replaces a single term occurrence. The position of this occurrence is given by the pos argument.
 *
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param pos The position of the term to be replaced within A. FIXME: I think it would be convenient to allow FOLPositions here.
 */
case class EqualityRightRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, pos: HOLPosition ) extends EqualityRule( subProof, eq, aux, pos ) {

  validateIndices( premise, Seq( eq ), Seq( aux ) )

  override def name = "eq:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object EqualityRightRule extends RuleConvenienceObject( "EqualityRightRule" ) {
  def apply( subProof: LKProof, eqFormula: HOLFormula, auxFormula: HOLFormula, main: HOLFormula ): EqualityRightRule = eqFormula match {
    case Eq( s, t ) =>
      val premise = subProof.endSequent

      val ( leftIndices, rightIndices ) = findAndValidate( premise )( Seq( eqFormula ), Seq( auxFormula ) )

      if ( s == t && auxFormula == main ) {
        val sAux = auxFormula.find( s )

        if ( sAux.isEmpty )
          throw LKRuleCreationException( "Eq is trivial, but term " + s + " does not occur in " + auxFormula + "." )

        EqualityRightRule( subProof, Ant( leftIndices( 0 ) ), Suc( rightIndices( 0 ) ), sAux.head )

      } else if ( s == t && auxFormula != main ) {
        throw LKRuleCreationException( "Eq is trivial, but aux formula " + auxFormula + " and main formula " + main + "differ." )

      } else if ( s != t && auxFormula == main ) {
        throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

      } else {
        val sAux = auxFormula.find( s )
        val sMain = main.find( s )

        val tAux = auxFormula.find( t )
        val tMain = main.find( t )

        if ( sAux.isEmpty && tAux.isEmpty )
          throw LKRuleCreationException( "Neither " + s + " nor " + t + " found in formula " + auxFormula + "." )

        val tToS = sMain intersect tAux
        val sToT = tMain intersect sAux

        if ( sToT.length == 1 && tToS.isEmpty ) {
          val p = sToT.head
          val mainNew = HOLPosition.replace( auxFormula, p, t )
          if ( mainNew == main ) {
            EqualityRightRule( subProof, Ant( leftIndices( 0 ) ), Suc( rightIndices( 0 ) ), p )
          } else throw LKRuleCreationException( "Replacement (" + auxFormula + ", " + p + ", " + t + ") should yield " + main + " but is " + mainNew + "." )
        } else if ( tToS.length == 1 && sToT.isEmpty ) {
          val p = tToS.head
          val mainNew = HOLPosition.replace( auxFormula, p, s )
          if ( mainNew == main ) {
            EqualityRightRule( subProof, Ant( leftIndices( 0 ) ), Suc( rightIndices( 0 ) ), p )
          } else throw LKRuleCreationException( "Replacement (" + auxFormula + ", " + p + ", " + s + ") should yield " + main + " but is " + mainNew + "." )
        } else throw LKRuleCreationException( "Formulas " + auxFormula + " and " + main + " don't differ in exactly one position." )
      }

    case _ => throw LKRuleCreationException( s"Formula $eqFormula is not an equation." )
  }

}

/**
 * An LKProof ending with an induction rule:
 *
 * <pre>
 *      (π1)                (π2)
 *  Γ :- Δ, A[0]    A[x], Π :- Λ, A[sx]
 * ------------------------------------ind
 *           Γ, Π :- Δ, Λ, A[t]
 * </pre>
 * Note that there is an eigenvariable condition on x, i.e. x must not occur freely in Π :- Λ.
 *
 * @param leftSubProof The subproof π,,1,,
 * @param aux1 The index of A[0].
 * @param rightSubProof The subproof π,,2,,
 * @param aux2 The index of A[x].
 * @param aux3 The index of A[sx].
 * @param term The term t in the conclusion.
 */
case class InductionRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex, aux3: SequentIndex, term: FOLTerm ) extends BinaryLKProof with CommonRule {
  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq( aux3 ) )

  private val zero = FOLConst( "0" )
  private def s( t: FOLTerm ) = FOLFunction( "s", List( t ) )

  override def name = "ind"

  // FIXME: Is there a better way than type casting?
  val ( aZero, aX, aSx ) = ( leftPremise( aux1 ).asInstanceOf[FOLFormula], rightPremise( aux2 ).asInstanceOf[FOLFormula], rightPremise( aux3 ).asInstanceOf[FOLFormula] )

  // Find a FOLSubstitution for A[x] and A[0], if possible.
  val sub1 = FOLMatchingAlgorithm.matchTerms( aX, aZero ) match {
    case Some( s ) => s
    case None      => throw LKRuleCreationException( s"Formula $aX can't be matched to formula $aZero." )
  }

  // Find a substitution for A[x] and A[Sx], if possible.
  val sub2 = FOLMatchingAlgorithm.matchTerms( aX, aSx ) match {
    case Some( s ) => s
    case None      => throw LKRuleCreationException( s"Formula $aX can't be matched to formula $aSx." )
  }

  val x = ( sub1.folmap ++ sub2.folmap ).collect { case ( v, e ) if v != e => v }.headOption.getOrElse {
    throw LKRuleCreationException( "Cannot determine induction variable." )
  }

  // Some safety checks
  if ( ( sub1.domain.toSet - x ).exists( v => sub1( v ) != v ) )
    throw LKRuleCreationException( s"Formula " + aX + " can't be matched to formula " + aZero + " by substituting a single variable." )

  if ( ( sub2.domain.toSet - x ).exists( v => sub1( v ) != v ) )
    throw LKRuleCreationException( s"Formula " + aX + " can't be matched to formula " + aSx + " by substituting a single variable." )

  val sX = s( x )

  if ( sub1( x ) != zero )
    throw LKRuleCreationException( s"$sub1 doesn't replace $x by 0." )

  if ( sub2( x ) != sX )
    throw LKRuleCreationException( s"$sub2 doesn't replace $x by $sX." )

  // Test the eigenvariable condition
  if ( ( rightPremise.delete( aux2 ).antecedent ++ rightPremise.delete( aux3 ).succedent ) map ( _.asInstanceOf[FOLFormula] ) flatMap freeVariables.apply contains x )
    throw LKRuleCreationException( s"Eigenvariable condition not satisified for sequent $rightPremise and variable $x." )

  // Construct the main formula
  val mainSub = FOLSubstitution( x, term )
  val mainFormula = mainSub( aX )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2, aux3 ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object InductionRule extends RuleConvenienceObject( "InductionRule" ) {
  /**
   * Convenience constructor that finds appropriate formula occurrences on its own.
   */
  def apply( leftSubProof: LKProof, inductionBase: FOLFormula, rightSubProof: LKProof, inductionHypo: FOLFormula, inductionStep: FOLFormula, term: FOLTerm ): InductionRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, indicesLeft ) = findAndValidate( leftPremise )( Seq(), Seq( inductionBase ) )
    val ( indicesRightAnt, indicesRightSuc ) = findAndValidate( rightPremise )( Seq( inductionHypo ), Seq( inductionStep ) )

    apply( leftSubProof, Suc( indicesLeft.head ), rightSubProof, Ant( indicesRightAnt.head ), Suc( indicesRightSuc.head ), term )
  }
}

/**
 * This class models the connection of formula occurrences between two sequents in a proof.
 *
 */
case class OccConnector( lowerSequent: HOLSequent, upperSequent: HOLSequent, parentsSequent: Sequent[Seq[SequentIndex]] ) {
  require( parentsSequent.sizes == lowerSequent.sizes )
  require( parentsSequent.elements.flatten.toSet subsetOf upperSequent.indices.toSet )

  def childrenSequent = upperSequent.indicesSequent map children

  /**
   * Given a SequentIndex for the lower sequent, this returns the list of parents of that occurrence in the upper sequent (if defined).
   *
   * @param idx
   * @return
   */
  def parents( idx: SequentIndex ): Seq[SequentIndex] = parentsSequent( idx )

  def parents[A]( lowerAs: Sequent[A] ): Sequent[Seq[A]] =
    childrenSequent map { _ map { lowerAs( _ ) } }

  /**
   * Given a SequentIndex for the upper sequent, this returns the list of children of that occurrence in the lower sequent (if defined).
   *
   * @param idx
   * @return
   */
  def children( idx: SequentIndex ): Seq[SequentIndex] =
    if ( upperSequent isDefinedAt idx )
      parentsSequent indicesWhere { _ contains idx }
    else
      throw new IndexOutOfBoundsException

  def *( that: OccConnector ) = {
    require( this.upperSequent == that.lowerSequent )
    OccConnector( this.lowerSequent, that.upperSequent, this.parentsSequent map { _ flatMap that.parents distinct } )
  }

  def inv: OccConnector = OccConnector( upperSequent, lowerSequent, childrenSequent )

  def +( that: OccConnector ) = {
    require( this.lowerSequent == that.lowerSequent )
    require( this.upperSequent == that.upperSequent )
    OccConnector( lowerSequent, upperSequent, lowerSequent.indicesSequent map { i => this.parents( i ) ++ that.parents( i ) } )
  }
}

object OccConnector {
  def apply( sequent: HOLSequent ): OccConnector = OccConnector( sequent, sequent, sequent.indicesSequent map { Seq( _ ) } )
}

object consoleString {
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
    val nLine = sys.props( "line.separator" )

    val upperNew = " " * Math.floor( upperDiff / 2 ).toInt + upperString + " " * Math.ceil( upperDiff / 2 ).toInt
    val lowerNew = " " * Math.floor( lowerDiff / 2 ).toInt + lowerString + " " * Math.ceil( lowerDiff / 2 ).toInt

    upperNew + nLine + line + ruleName + nLine + lowerNew
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

/**
 * Class for reducing boilerplate code in LK companion objects.
 *
 * @param longName The long name of the rule.
 */
private[lkNew] class RuleConvenienceObject( val longName: String ) {
  /**
   * Create an LKRuleCreationException with a message starting with "Cannot create $longName: ..."
   *
   * @param text The rest of the message.
   * @return
   */
  protected def LKRuleCreationException( text: String ): LKRuleCreationException = new LKRuleCreationException( longName, text )

  /**
   * Method to determine the indices of formulas in a sequent.
   *
   * If either list contains duplicate formulas, each duplicate that can't be found will induce a -1 in the output.
   *
   * @param premise The sequent to find formulas in.
   * @param antFormulas Formulas to be found in the antecedent.
   * @param sucFormulas Formulas to be found in the succedent.
   * @return
   */
  protected def findFormulasInPremise( premise: HOLSequent )( antFormulas: Seq[HOLFormula], sucFormulas: Seq[HOLFormula] ): ( Seq[Int], Seq[Int] ) = {
    val antMap = scala.collection.mutable.HashMap.empty[HOLFormula, Int]
    val sucMap = scala.collection.mutable.HashMap.empty[HOLFormula, Int]

    val antIndices = for ( f <- antFormulas ) yield if ( antMap contains f ) {
      val i = antMap( f )
      val iNew = premise.antecedent.indexOf( f, i + 1 )

      antMap += ( f -> iNew )
      iNew
    } else {
      val iNew = premise.antecedent.indexOf( f )

      antMap += ( f -> iNew )
      iNew
    }

    val sucIndices = for ( f <- sucFormulas ) yield if ( sucMap contains f ) {
      val i = sucMap( f )
      val iNew = premise.succedent.indexOf( f, i + 1 )

      sucMap += ( f -> iNew )
      iNew
    } else {
      val iNew = premise.succedent.indexOf( f )

      sucMap += ( f -> iNew )
      iNew
    }

    ( antIndices, sucIndices )
  }

  /**
   * Throws an exception if the output of findFormulasInPremise contains any -1 entries.
   *
   * @param premise The sequent in question.
   * @param antFormulas The list of formulas in the antecedent.
   * @param antIndices The list of indices corresponding to antFormulas.
   * @param sucFormulas The list of formulas in the succedent.
   * @param sucIndices The list indices corresponding to sucFormulas.
   * @return
   */
  protected def validateIndices( premise: HOLSequent )( antFormulas: Seq[HOLFormula], antIndices: Seq[Int], sucFormulas: Seq[HOLFormula], sucIndices: Seq[Int] ) = {
    val antMap = scala.collection.mutable.HashMap.empty[HOLFormula, Int]
    val sucMap = scala.collection.mutable.HashMap.empty[HOLFormula, Int]

    for ( ( f, i ) <- antFormulas zip antIndices ) {
      val count = antMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw LKRuleCreationException( s"Formula $f only found $count times in antecedent of $premise." )

      antMap += f -> ( count + 1 )
    }

    for ( ( f, i ) <- sucFormulas zip sucIndices ) {
      val count = sucMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw LKRuleCreationException( s"Formula $f only found $count times in succedent of $premise." )

      sucMap += f -> ( count + 1 )
    }

  }

  /**
   * Combines findFormulasInPremise and validateIndices. That is, it will return a pair of lists of indices and throw an exception if either
   * list contains a -1.
   *
   * @param premise
   * @param antFormulas
   * @param sucFormulas
   * @return
   */
  protected def findAndValidate( premise: HOLSequent )( antFormulas: Seq[HOLFormula], sucFormulas: Seq[HOLFormula] ): ( Seq[Int], Seq[Int] ) = {
    val ( antIndices, sucIndices ) = findFormulasInPremise( premise )( antFormulas, sucFormulas )
    validateIndices( premise )( antFormulas, antIndices, sucFormulas, sucIndices )
    ( antIndices, sucIndices )
  }
}

class LKRuleCreationException( name: String, message: String ) extends Exception( s"Cannot create $name: " + message )
