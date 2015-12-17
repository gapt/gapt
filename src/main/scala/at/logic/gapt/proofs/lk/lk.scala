package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ FOLPosition, FOLSubstitution, FOLMatchingAlgorithm }
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.utils.dssupport.ListSupport.pairs

import scala.collection.mutable

abstract class LKProof extends SequentProof[HOLFormula, LKProof] {

  def LKRuleCreationException( message: String ): LKRuleCreationException = new LKRuleCreationException( longName, message )

  /**
   * The end-sequent of the rule.
   */
  final def endSequent = conclusion

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
   * The object connecting the lower and upper sequents.auxFormulas
   *
   * @return
   */
  def getOccConnector: OccConnector[HOLFormula] = occConnectors.head

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
  def getLeftOccConnector: OccConnector[HOLFormula] = occConnectors.head

  /**
   * The object connecting the lower and right upper sequents.
   *
   * @return
   */
  def getRightOccConnector: OccConnector[HOLFormula] = occConnectors.tail.head

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

trait CommonRule extends LKProof with ContextRule[HOLFormula, LKProof]

/**
 * Use this trait for rules that use eigenvariables.
 *
 */
trait Eigenvariable {
  def eigenVariable: Var
}

object Eigenvariable {
  /**
   * A proof matches Eigenvariable(v) if its bottommost inference uses the eigenvariable v.
   *
   * @param proof An LKProof
   * @return
   */
  def unapply( proof: LKProof ) = proof match {
    case p: Eigenvariable => Some( p.eigenVariable )
    case _                => None
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

case class TheoryAxiom( conclusion: Sequent[HOLAtom] ) extends InitialSequent

/**
 * An LKProof introducing ⊤ on the right:
 * <pre>
 *       --------⊤:r
 *         :- ⊤
 * </pre>
 */
case object TopAxiom extends InitialSequent {
  override def name: String = "⊤:r"
  override def conclusion = HOLSequent( Nil, Seq( Top() ) )
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
  override def conclusion = HOLSequent( Seq( Bottom() ), Nil )
  def mainFormula = Bottom()
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
case class LogicalAxiom( A: HOLFormula ) extends InitialSequent {
  override def conclusion = HOLSequent( Seq( A ), Seq( A ) )
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
  override def conclusion = HOLSequent( Seq(), Seq( Eq( s, s ) ) )
  def mainFormula = Eq( s, s )
}

/**
 * Convenience object for constructing Axioms.
 *
 */
object Axiom {
  /**
   * Convenience constructor for axioms.
   *
   * @param sequent A HOLSequent.
   * @return An axiom of the appropriate type, depending on sequent.
   */
  def apply( sequent: HOLSequent ): InitialSequent = sequent match {
    case Sequent( Seq( f ), Seq( g ) ) if f == g => LogicalAxiom( f )
    case Sequent( Seq(), Seq( Top() ) ) => TopAxiom
    case Sequent( Seq( Bottom() ), Seq() ) => BottomAxiom
    case Sequent( Seq(), Seq( Eq( s: LambdaExpression, t: LambdaExpression ) ) ) if s == t => ReflexivityAxiom( s )
    case _ if sequent.forall( _.isInstanceOf[HOLAtom] ) => TheoryAxiom( sequent.asInstanceOf[Sequent[HOLAtom]] )

    case _ => throw new IllegalArgumentException( s"Cannot create axiom from sequent $sequent." )
  }

  /**
   * Convenience constructor for axioms.
   *
   * @param ant A list of HOLFormulas.
   * @param suc A list of HOLFormulas.
   * @return An axiom of the appropriate type, depending on ant and suc.
   */
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
case class ContractionLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliar formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  val mainFormula = premise( aux1 )

  override def name = "c:l"

  override def mainFormulaSequent = mainFormula +: Sequent()

}

object ContractionLeftRule extends ConvenienceConstructor( "ContractionLeftRule" ) {
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
case class ContractionRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux1, aux2 ) )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliar formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  val mainFormula = premise( aux1 )

  override def name = "c:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula

}

object ContractionRightRule extends ConvenienceConstructor( "ContractionRightRule" ) {
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
case class WeakeningLeftRule( subProof: LKProof, formula: HOLFormula )
    extends UnaryLKProof with CommonRule {
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
case class WeakeningRightRule( subProof: LKProof, formula: HOLFormula )
    extends UnaryLKProof with CommonRule {
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
case class CutRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
    extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  if ( leftPremise( aux1 ) != rightPremise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliar formulas are not the same." )

  def cutFormula = leftPremise( aux1 )

  override def name = "cut"

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def mainFormulaSequent = Sequent()
}

object CutRule extends ConvenienceConstructor( "CutRule" ) {

  /**
   * Convenience constructor for cut.
   * Each of the cut formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param leftCutFormula Index of the left cut formula or the formula itself.
   * @param rightSubProof The right subproof.
   * @param rightCutFormula Index of the right cut formula or the formula itself.
   * @return
   */
  def apply( leftSubProof: LKProof, leftCutFormula: IndexOrFormula, rightSubProof: LKProof, rightCutFormula: IndexOrFormula ): CutRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, sucIndices ) = findAndValidate( leftPremise )( Seq(), Seq( leftCutFormula ) )
    val ( antIndices, _ ) = findAndValidate( rightPremise )( Seq( rightCutFormula ), Seq() )

    new CutRule( leftSubProof, Suc( sucIndices( 0 ) ), rightSubProof, Ant( antIndices( 0 ) ) )

  }

  /**
   * Convenience constructor for cut.
   * Given a cut formula, it will attempt to create a cut inference with that formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param cutFormula The cut formula.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, cutFormula: HOLFormula ): CutRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, sucIndices ) = findAndValidate( leftPremise )( Seq(), Seq( cutFormula ) )
    val ( antIndices, _ ) = findAndValidate( rightPremise )( Seq( cutFormula ), Seq() )

    new CutRule( leftSubProof, Suc( sucIndices( 0 ) ), rightSubProof, Ant( antIndices( 0 ) ) )
  }
}

/**
 * Index of the left cut formula or the formula itself.
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
case class NegLeftRule( subProof: LKProof, aux: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  val mainFormula = Neg( premise( aux ) )

  override def auxIndices = Seq( Seq( aux ) )
  override def name = "¬:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object NegLeftRule extends ConvenienceConstructor( "NegLeftRule" ) {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof The subproof.
   * @param auxFormula The formula to be negated.
   * @return
   */
  def apply( subProof: LKProof, auxFormula: HOLFormula ): NegLeftRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

    new NegLeftRule( subProof, Suc( indices( 0 ) ) )
  }
}

/**
 * An LKProof ending with a negation on the right:Index of the left cut formula or the formula itself.
 * <pre>
 *       (π)
 *    A, Γ :- Δ
 *   -----------¬:r
 *   Γ :- Δ, ¬A
 * </pre>
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 */
case class NegRightRule( subProof: LKProof, aux: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  val mainFormula = Neg( premise( aux ) )

  override def auxIndices = Seq( Seq( aux ) )
  override def name = "¬:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object NegRightRule extends ConvenienceConstructor( "NegRightRule" ) {
  /**
   * Convenience constructor that automatically uses the first occurrence of supplied aux formula.
   *
   * @param subProof The subproof.
   * @param auxFormula The formula to be negated.
   * @return
   */
  def apply( subProof: LKProof, auxFormula: HOLFormula ): NegRightRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Seq() )

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
 * @param aux1 The index of A.
 * @param aux2 The index of B.
 */
case class AndLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  val leftConjunct = premise( aux1 )
  val rightConjunct = premise( aux2 )
  val mainFormula = And( leftConjunct, rightConjunct )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∧:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object AndLeftRule extends ConvenienceConstructor( "AndLeftRule" ) {

  /**
   * Convenience constructor for ∧:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftConjunct Index of the left conjunct or the conjunct itself.
   * @param rightConjunct Index of the right conjunct or the conjunct itself.
   * @return
   */
  def apply( subProof: LKProof, leftConjunct: Either[SequentIndex, HOLFormula], rightConjunct: Either[SequentIndex, HOLFormula] ): AndLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( leftConjunct, rightConjunct ), Seq() )

    AndLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
  }

  /**
   * Convenience constructor for ∧:l.
   * Given a proposed main formula A ∧ B, it will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The main formula to be inferred. Must be of the form A ∧ B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula ): AndLeftRule = mainFormula match {
    case And( f, g ) => apply( subProof, f, g )
    case _           => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
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
case class AndRightRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
    extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq(), Seq( aux2 ) )

  val leftConjunct = leftPremise( aux1 )
  val rightConjunct = rightPremise( aux2 )

  val mainFormula = And( leftConjunct, rightConjunct )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "∧:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object AndRightRule extends ConvenienceConstructor( "AndRightRule" ) {

  /**
   * Convenience constructor for ∧:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param leftConjunct Index of the left conjunct or the conjunct itself.
   * @param rightSubProof The right subproof.
   * @param rightConjunct Index of the right conjunct or the conjunct itself.
   * @return
   */
  def apply( leftSubProof: LKProof, leftConjunct: IndexOrFormula, rightSubProof: LKProof, rightConjunct: IndexOrFormula ): AndRightRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, leftIndices ) = findAndValidate( leftPremise )( Seq(), Seq( leftConjunct ) )
    val ( _, rightIndices ) = findAndValidate( rightPremise )( Seq(), Seq( rightConjunct ) )

    new AndRightRule( leftSubProof, Suc( leftIndices( 0 ) ), rightSubProof, Suc( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for ∧:r.
   * Given a proposed main formula A ∧ B, it will attempt to create an inference with this main formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∧ B.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: HOLFormula ): AndRightRule = mainFormula match {
    case And( f, g ) => apply( leftSubProof, f, rightSubProof, g )
    case _           => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
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
case class OrLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
    extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq( aux1 ), Seq() )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  val leftDisjunct = leftPremise( aux1 )
  val rightDisjunct = rightPremise( aux2 )

  val mainFormula = Or( leftDisjunct, rightDisjunct )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "∨:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object OrLeftRule extends ConvenienceConstructor( "OrLeftRule" ) {

  /**
   * Convenience constructor for ∨:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param leftDisjunct Index of the left disjunct or the disjunct itself.
   * @param rightSubProof The right subproof.
   * @param rightDisjunct Index of the right disjunct or the disjunct itself.
   * @return
   */
  def apply( leftSubProof: LKProof, leftDisjunct: IndexOrFormula, rightSubProof: LKProof, rightDisjunct: IndexOrFormula ): OrLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( leftIndices, _ ) = findAndValidate( leftPremise )( Seq( leftDisjunct ), Seq() )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( rightDisjunct ), Seq() )

    new OrLeftRule( leftSubProof, Ant( leftIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for ∨:r.
   * Given a proposed main formula A ∨ B, it will attempt to create an inference with this main formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∨ B.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: HOLFormula ): OrLeftRule = mainFormula match {
    case Or( f, g ) => apply( leftSubProof, f, rightSubProof, g )
    case _          => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a disjunction." )
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
case class OrRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux1, aux2 ) )

  val leftDisjunct = premise( aux1 )
  val rightDisjunct = premise( aux2 )
  val mainFormula = Or( leftDisjunct, rightDisjunct )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∨:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object OrRightRule extends ConvenienceConstructor( "OrRightRule" ) {

  /**
   * Convenience constructor for ∨:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param leftDisjunct Index of the left disjunct or the disjunct itself.
   * @param rightDisjunct Index of the right disjunct or the disjunct itself.
   * @return
   */
  def apply( subProof: LKProof, leftDisjunct: IndexOrFormula, rightDisjunct: IndexOrFormula ): OrRightRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( leftDisjunct, rightDisjunct ) )

    new OrRightRule( subProof, Suc( indices( 0 ) ), Suc( indices( 1 ) ) )
  }

  /**
   * Convenience constructor for ∨:r that, given a proposed main formula A ∨ B, will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∨ B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula ): OrRightRule = mainFormula match {
    case Or( f, g ) => apply( subProof, f, g )
    case _          => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a disjunction." )
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
case class ImpLeftRule( leftSubProof: LKProof, aux1: SequentIndex, rightSubProof: LKProof, aux2: SequentIndex )
    extends BinaryLKProof with CommonRule {

  validateIndices( leftPremise, Seq(), Seq( aux1 ) )
  validateIndices( rightPremise, Seq( aux2 ), Seq() )

  val impPremise = leftPremise( aux1 )
  val impConclusion = rightPremise( aux2 )

  val mainFormula = Imp( impPremise, impConclusion )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "\u2283:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ImpLeftRule extends ConvenienceConstructor( "ImpLeftRule" ) {

  /**
   * Convenience constructor for →:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param leftSubProof The left subproof.
   * @param impPremise Index of the premise of the implication or the premise itself.
   * @param rightSubProof The right subproof.
   * @param impConclusion Index of the conclusion of the implication or the conclusion itself.
   * @return
   */
  def apply( leftSubProof: LKProof, impPremise: IndexOrFormula, rightSubProof: LKProof, impConclusion: IndexOrFormula ): ImpLeftRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, leftIndices ) = findAndValidate( leftPremise )( Seq(), Seq( impPremise ) )
    val ( rightIndices, _ ) = findAndValidate( rightPremise )( Seq( impConclusion ), Seq() )

    new ImpLeftRule( leftSubProof, Suc( leftIndices( 0 ) ), rightSubProof, Ant( rightIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:l.
   * Given a proposed main formula A → B, it will attempt to create an inference with this main formula.
   *
   * @param leftSubProof The left subproof.
   * @param rightSubProof The right subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A → B.
   * @return
   */
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: HOLFormula ): ImpLeftRule = mainFormula match {
    case Imp( f, g ) => apply( leftSubProof, f, rightSubProof, g )
    case _           => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a implication." )
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
case class ImpRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux1 ), Seq( aux2 ) )

  val impPremise = premise( aux1 )
  val impConclusion = premise( aux2 )
  val mainFormula = Imp( impPremise, impConclusion )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "\u2283:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ImpRightRule extends ConvenienceConstructor( "ImpRightRule" ) {

  /**
   * Convenience constructor for →:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param impPremise Index of the premise of the implication or the premise itself.
   * @param impConclusion Index of the conclusion of the implication or the conclusion itself.
   * @return
   */
  def apply( subProof: LKProof, impPremise: IndexOrFormula, impConclusion: IndexOrFormula ): ImpRightRule = {
    val premise = subProof.endSequent

    val ( antIndices, sucIndices ) = findAndValidate( premise )( Seq( impPremise ), Seq( impConclusion ) )

    new ImpRightRule( subProof, Ant( antIndices( 0 ) ), Suc( sucIndices( 0 ) ) )
  }

  /**
   * Convenience constructor for →:r that, given a proposed main formula A → B, will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A → B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula ): ImpRightRule = mainFormula match {
    case Imp( f, g ) => apply( subProof, f, g )
    case _           => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not an implication." )
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
case class ForallLeftRule( subProof: LKProof, aux: SequentIndex, A: HOLFormula, term: LambdaExpression, v: Var )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  if ( premise( aux ) != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula = All( v, A )

  override def name = "∀:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ForallLeftRule extends ConvenienceConstructor( "ForallLeftRule" ) {
  /**
   * Convenience constructor for ∀:l that, given a main formula and a term, will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A.
   * @param term A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula, term: LambdaExpression ): ForallLeftRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )
        val i = premise.antecedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in antecedent of $premise." )

        ForallLeftRule( subProof, Ant( i ), subFormula, term, v )

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
    }
  }

  /**
   * Convenience constructor for ∀:l that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A. The premise must contain A.
   * @return
   */
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
case class ForallRightRule( subProof: LKProof, aux: SequentIndex, eigenVariable: Var, quantifiedVariable: Var )
    extends UnaryLKProof with CommonRule with Eigenvariable {

  validateIndices( premise, Seq(), Seq( aux ) )

  val ( auxFormula, context ) = premise focus aux

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw LKRuleCreationException( s"Eigenvariable condition is violated: $context contains $eigenVariable" )

  val subFormula = BetaReduction.betaNormalize( Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  if ( BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) != auxFormula )
    throw LKRuleCreationException( s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = ${BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) )}, but is $auxFormula." )

  val mainFormula = All( quantifiedVariable, subFormula )

  override def name = "∀:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallRightRule extends ConvenienceConstructor( "ForallRightRule" ) {

  /**
   * Convenience constructor for ∀:r that, given a main formula and an eigenvariable, will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula, eigenVariable: Var ): ForallRightRule = mainFormula match {
    case All( v, subFormula ) =>
      val auxFormula = Substitution( v, eigenVariable )( subFormula )

      val premise = subProof.endSequent

      val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

      ForallRightRule( subProof, Suc( indices( 0 ) ), eigenVariable, v )

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }

  /**
   * Convenience constructor for ∀:r that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A. The premise must contain A.
   * @return
   */
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
case class ExistsLeftRule( subProof: LKProof, aux: SequentIndex, eigenVariable: Var, quantifiedVariable: Var )
    extends UnaryLKProof with CommonRule with Eigenvariable {

  validateIndices( premise, Seq( aux ), Seq() )

  val ( auxFormula, context ) = premise focus aux

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw LKRuleCreationException( s"Eigenvariable condition is violated: $context contains $eigenVariable" )

  val subFormula = BetaReduction.betaNormalize( Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  if ( BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) != auxFormula )
    throw LKRuleCreationException( s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = ${BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) )}, but is $auxFormula." )

  val mainFormula = Ex( quantifiedVariable, subFormula )

  override def name = "∃:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ExistsLeftRule extends ConvenienceConstructor( "ExistsLeftRule" ) {

  /**
   * Convenience constructor for ∃:l that, given a main formula and an eigenvariable, will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula, eigenVariable: Var ): ExistsLeftRule = mainFormula match {
    case Ex( v, subFormula ) =>
      val auxFormula = Substitution( v, eigenVariable )( subFormula )

      val premise = subProof.endSequent

      val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Seq() )
      ExistsLeftRule( subProof, Ant( indices( 0 ) ), eigenVariable, v )

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }

  /**
   * Convenience constructor for ∃:l that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A. The premise must contain A.
   * @return
   */
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
case class ExistsRightRule( subProof: LKProof, aux: SequentIndex, A: HOLFormula, term: LambdaExpression, v: Var )
    extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  if ( premise( aux ) != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula = Ex( v, A )

  override def name = "∃:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ExistsRightRule extends ConvenienceConstructor( "ExistsRightRule" ) {

  /**
   * Convenience constructor for ∃:r that, given a main formula and a term, will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A.
   * @param term A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: HOLFormula, term: LambdaExpression ): ExistsRightRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case Ex( v, subFormula ) =>
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )
        val i = premise.succedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in succedent of $premise." )

        ExistsRightRule( subProof, Suc( i ), subFormula, term, v )

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
    }
  }

  /**
   * Convenience constructor for ∃:r that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A. The premise must contain A.
   * @return
   */
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
 */
abstract class EqualityRule extends UnaryLKProof with CommonRule {

  def subProof: LKProof
  def eq: SequentIndex
  def aux: SequentIndex
  def positions: Seq[HOLPosition]

  require( positions.nonEmpty, "Replacement at zero positions is not supported at this time." )

  aux match {
    case Ant( _ ) => validateIndices( premise, Seq( eq, aux ), Seq() )
    case Suc( _ ) => validateIndices( premise, Seq( eq ), Seq( aux ) )
  }

  val equation = premise( eq )

  val auxFormula = premise( aux )

  val first = positions.head

  val ( what, by, leftToRight ) = equation match {
    case Eq( s, t ) =>
      auxFormula( first ) match {
        case `s` =>
          ( s, t, true )
        case `t` =>
          ( t, s, false )
        case _ =>
          throw LKRuleCreationException( s"Position $first in $auxFormula should be $s or $t, but is ${auxFormula( first )}." )
      }
    case _ => throw LKRuleCreationException( s"Formula $equation is not an equation." )
  }

  val mainFormula = positions.foldLeft( auxFormula ) { ( acc, p ) =>
    require( acc( p ) == what, s"Position $p in $acc should be $what, but is ${acc( p )}." )

    acc.replace( p, by )
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
 * In either case, the rule only replaces term occurrences at parallel positions. These positions are given by the positions argument.
 *
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param positions The positions of the term to be replaced within A.
 */
case class EqualityLeftRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, positions: Seq[HOLPosition] )
    extends EqualityRule {

  validateIndices( premise, Seq( eq, aux ), Seq() )

  override def name = "eq:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object EqualityLeftRule extends ConvenienceConstructor( "EqualityLeftRule" ) {

  /**
   * Convenience constructor for eq:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eqFormula The index of the equation or the equation itself.
   * @param auxFormula The index of the auxiliary formula or the formula itself.
   * @param pos The positions of the term to be replaced within A.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula, pos: Seq[HOLPosition] ): EqualityLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( eqFormula, auxFormula ), Seq() )

    EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), pos )

  }

  /**
   * Convenience constructor for eq:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eqFormula The index of the equation or the equation itself.
   * @param auxFormula The index of the auxiliary formula or the formula itself.
   * @param pos The positions of the term to be replaced within A.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula, pos: Seq[FOLPosition] )( implicit dummyImplicit: DummyImplicit ): EqualityLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( eqFormula, auxFormula ), Seq() )

    val aF = premise( Ant( indices( 1 ) ) ) match {
      case f: FOLFormula =>
        f
      case _ =>
        throw LKRuleCreationException( s"Proposed aux formula ${premise( Ant( indices( 1 ) ) )} is not FOL." )
    }

    EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), pos map { FOLPosition.toHOLPosition( aF ) } )
  }

  /**
   * Convenience constructor for eq:l.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eq The index of the equation or the equation itself.
   * @param aux The index of the auxiliary formula or the formula itself.
   * @param mainFormula The proposed main formula.
   * @return
   */
  def apply( subProof: LKProof, eq: IndexOrFormula, aux: IndexOrFormula, mainFormula: HOLFormula ): EqualityLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( eq, aux ), Seq() )
    val ( eqFormula, auxFormula ) = ( premise( Ant( indices( 0 ) ) ), premise( Ant( indices( 1 ) ) ) )

    eqFormula match {
      case Eq( s, t ) =>
        if ( s == t && auxFormula == mainFormula ) {
          val sAux = auxFormula.find( s )

          if ( sAux.isEmpty )
            throw LKRuleCreationException( "Eq is trivial, but term " + s + " does not occur in " + auxFormula + "." )

          EqualityLeftRule( subProof, eq, aux, Seq( sAux.head ) )

        } else if ( s == t && auxFormula != mainFormula ) {
          throw LKRuleCreationException( "Eq is trivial, but aux formula " + auxFormula + " and main formula " + mainFormula + "differ." )

        } else if ( s != t && auxFormula == mainFormula ) {
          throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

        } else {
          val sAux = auxFormula.find( s )
          val sMain = mainFormula.find( s )

          val tAux = auxFormula.find( t )
          val tMain = mainFormula.find( t )

          if ( sAux.isEmpty && tAux.isEmpty )
            throw LKRuleCreationException( "Neither " + s + " nor " + t + " found in formula " + auxFormula + "." )

          val tToS = sMain intersect tAux
          val sToT = tMain intersect sAux

          if ( tToS.isEmpty ) {
            val mainNew = auxFormula.replace( sToT, t )
            if ( mainNew == mainFormula ) {
              EqualityLeftRule( subProof, eq, aux, sToT )
            } else throw LKRuleCreationException( "Replacement should yield " + mainFormula + " but is " + mainNew + "." )
          } else if ( sToT.isEmpty ) {
            val mainNew = auxFormula.replace( tToS, s )
            if ( mainNew == mainFormula ) {
              EqualityLeftRule( subProof, eq, aux, tToS )
            } else throw LKRuleCreationException( "Replacement should yield " + mainFormula + " but is " + mainNew + "." )
          } else throw LKRuleCreationException( "Cannot perform replacements in both directions in " + auxFormula + " and " + mainFormula + "." )
        }

      case _ => throw LKRuleCreationException( s"Formula $eqFormula is not an equation." )
    }
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
 * In either case, the rule only replaces term occurrences at parallel positions. These positions are given by the positions argument.
 *
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param positions The positions of the term to be replaced within A.
 */
case class EqualityRightRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, positions: Seq[HOLPosition] )
    extends EqualityRule {

  validateIndices( premise, Seq( eq ), Seq( aux ) )

  override def name = "eq:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object EqualityRightRule extends ConvenienceConstructor( "EqualityRightRule" ) {

  /**
   * Convenience constructor for eq:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eqFormula The index of the equation or the equation itself.
   * @param auxFormula The index of the auxiliary formula or the formula itself.
   * @param pos The positions of the term to be replaced within A.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula, pos: Seq[HOLPosition] ): EqualityRightRule = {
    val premise = subProof.endSequent

    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eqFormula ), Seq( auxFormula ) )

    EqualityRightRule( subProof, Ant( indicesAnt( 0 ) ), Suc( indicesSuc( 0 ) ), pos )

  }

  /**
   * Convenience constructor for eq:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eqFormula The index of the equation or the equation itself.
   * @param auxFormula The index of the auxiliary formula or the formula itself.
   * @param pos The positions of the term to be replaced within A.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula, pos: Seq[FOLPosition] )( implicit dummyImplicit: DummyImplicit ): EqualityRightRule = {
    val premise = subProof.endSequent

    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eqFormula ), Seq( auxFormula ) )

    val aF = premise( Suc( indicesSuc( 0 ) ) ) match {
      case f: FOLFormula =>
        f
      case _ =>
        throw LKRuleCreationException( s"Proposed aux formula ${premise( Suc( indicesSuc( 0 ) ) )} is not FOL." )
    }

    EqualityRightRule( subProof, Ant( indicesAnt( 0 ) ), Suc( indicesSuc( 0 ) ), pos map { FOLPosition.toHOLPosition( aF ) } )

  }

  /**
   * Convenience constructor for eq:r.
   * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
   * will attempt to find an appropriate index on its own.
   *
   * @param subProof The subproof.
   * @param eq The index of the equation or the equation itself.
   * @param aux The index of the auxiliary formula or the formula itself.
   * @param mainFormula The proposed main formula.
   * @return
   */
  def apply( subProof: LKProof, eq: IndexOrFormula, aux: IndexOrFormula, mainFormula: HOLFormula ): EqualityRightRule = {
    val premise = subProof.endSequent
    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eq ), Seq( aux ) )
    val ( eqFormula, auxFormula ) = ( premise( Ant( indicesAnt( 0 ) ) ), premise( Suc( indicesSuc( 0 ) ) ) )

    eqFormula match {
      case Eq( s, t ) =>
        if ( s == t && auxFormula == mainFormula ) {
          val sAux = auxFormula.find( s )

          if ( sAux.isEmpty )
            throw LKRuleCreationException( "Eq is trivial, but term " + s + " does not occur in " + auxFormula + "." )

          EqualityRightRule( subProof, eq, aux, sAux )

        } else if ( s == t && auxFormula != mainFormula ) {
          throw LKRuleCreationException( "Eq is trivial, but aux formula " + auxFormula + " and main formula " + mainFormula + "differ." )

        } else if ( s != t && auxFormula == mainFormula ) {
          throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

        } else {
          val sAux = auxFormula.find( s )
          val sMain = mainFormula.find( s )

          val tAux = auxFormula.find( t )
          val tMain = mainFormula.find( t )

          if ( sAux.isEmpty && tAux.isEmpty )
            throw LKRuleCreationException( "Neither " + s + " nor " + t + " found in formula " + auxFormula + "." )

          val tToS = sMain intersect tAux
          val sToT = tMain intersect sAux

          if ( tToS.isEmpty ) {
            val mainNew = auxFormula.replace( sToT, t )
            if ( mainNew == mainFormula ) {
              EqualityRightRule( subProof, eq, aux, sToT )
            } else throw LKRuleCreationException( "Replacement should yield " + mainFormula + " but is " + mainNew + "." )
          } else if ( sToT.isEmpty ) {
            val mainNew = auxFormula.replace( tToS, s )
            if ( mainNew == mainFormula ) {
              EqualityRightRule( subProof, eq, aux, tToS )
            } else throw LKRuleCreationException( "Replacement should yield " + mainFormula + " but is " + mainNew + "." )
          } else throw LKRuleCreationException( "Cannot perform replacements in both directions in " + auxFormula + " and " + mainFormula + "." )
        }

      case _ => throw LKRuleCreationException( s"Formula $eqFormula is not an equation." )
    }
  }
}

/**
 * Proof that a given data type constructor c preserves a formula F:
 *
 * <pre>
 *                                  (π)
 * F(x,,1,,), F(x,,2,,), ..., F(x,,n,,), Γ :- Δ, F(c(x,,1,,,...,x,,n,,,y,,1,,,...,y,,n,,))
 * </pre>
 *
 * The variables x,,i,, and y,,i,, are eigenvariables; x,,i,, are the eigenvariables of the same type as the inductive data
 * type, y,,i,, are the other arguments of the constructor c.  They can come in any order in the constructor.
 *
 * @param proof  The LKProof ending in the sequent of this case.
 * @param constructor  The constructor c of the inductive data type that we're considering.
 * @param hypotheses  Indices of F(x,,1,,), ..., F(x,,n,,)
 * @param eigenVars  The eigenvariables of this case: x,,1,,, ..., x,,n,,, y,,1,,, ..., y,,n,,  (these need to correspond to the order in c)
 * @param conclusion  Index of F(c(x,,1,,,...,x,,n,,,y,,1,,,...,y,,n,,))
 */
case class InductionCase( proof: LKProof, constructor: Const,
                          hypotheses: Seq[SequentIndex], eigenVars: Seq[Var],
                          conclusion: SequentIndex ) {
  val FunctionType( indTy, fieldTypes ) = constructor.exptype
  require( fieldTypes == eigenVars.map( _.exptype ) )

  val hypVars = eigenVars filter { _.exptype == indTy }
  require( hypotheses.size == hypVars.size )

  hypotheses foreach { hyp =>
    require( hyp.isAnt && proof.endSequent.isDefinedAt( hyp ) )
  }

  require( conclusion.isSuc && proof.endSequent.isDefinedAt( conclusion ) )
}

/**
 * An LKProof ending with an induction rule:
 * <pre>
 *   (π,,1,,)   (π,,2,,)           (π,,n,,)
 * case 1      case 2     ...     case n
 * -------------------------------------(ind)
 * Γ :- Δ, ∀x: indTy, F(x)
 * </pre>
 *
 * This induction rule can handle inductive data types.
 * The cases are proofs that the various type constructors preserve the formula we want to prove. They are provided via the
 * [[InductionCase]] class.
 *
 * @param cases A sequence of proofs showing that each type constructor preserves the validity of the main formula.
 * @param mainFormula The formula we want to prove via induction.
 */
case class InductionRule( cases: Seq[InductionCase], mainFormula: HOLFormula ) extends CommonRule {
  val All( quant @ Var( _, indTy ), qfFormula ) = mainFormula
  cases foreach { c =>
    require( c.indTy == indTy )
    ( c.hypotheses, c.hypVars ).zipped foreach { ( hyp, eigen ) =>
      require( c.proof.endSequent( hyp ) == Substitution( quant -> eigen )( qfFormula ) )
    }
    require( c.proof.endSequent( c.conclusion ) == Substitution( quant -> c.constructor( c.eigenVars: _* ) )( qfFormula ) )
  }
  require( freeVariables( contexts.flatMap( _.elements ) :+ mainFormula ) intersect cases.flatMap( _.eigenVars ).toSet isEmpty )

  override protected def mainFormulaSequent = Sequent() :+ mainFormula
  override def auxIndices: Seq[Seq[SequentIndex]] = cases map { c => c.hypotheses :+ c.conclusion }
  override def immediateSubProofs: Seq[LKProof] = cases map { _.proof }

  private lazy val product = cases.flatMap { _.productIterator } :+ mainFormula
  override def productArity = product.size
  override def productElement( n: Int ) = product( n )

  override def name = "ind"
}

/**
 * An LKProof ending with a definition on the left:
 *
 * <pre>
 *       (π)
 *    A, Γ :- Δ
 *   -----------d:l
 *    B, Γ :- Δ
 * </pre>
 *
 * Currently, the formulas A and B can be completely arbitrary.
 *
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 * @param main The formula B that A is to be replaced with.
 */
case class DefinitionLeftRule( subProof: LKProof, aux: SequentIndex, main: HOLFormula )
    extends UnaryLKProof with CommonRule {
  override def name = "d:l"
  override def auxIndices = Seq( Seq( aux ) )
  override def mainFormulaSequent = main +: Sequent()
}

object DefinitionLeftRule extends ConvenienceConstructor( "DefinitionLeftRule" ) {

  /**
   * Convenience constructor for d:l that, given an aux and main formula, will attempt to infer the main formula.
   *
   * @param subProof The subproof.
   * @param auxFormula The aux formula.
   * @param mainFormula The main formula.
   * @return
   */
  def apply( subProof: LKProof, auxFormula: HOLFormula, mainFormula: HOLFormula ): DefinitionLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Seq() )

    DefinitionLeftRule( subProof, Ant( indices( 0 ) ), mainFormula )
  }
}

/**
 * An LKProof ending with a definition on the right:
 *
 * <pre>
 *       (π)
 *    Γ :- Δ, A
 *   -----------d:l
 *    Γ :- Δ, B
 * </pre>
 *
 * Currently, the formulas A and B can be completely arbitrary.
 *
 * @param subProof The proof π.
 * @param aux The index of A in the succedent.
 * @param main The formula B that A is to be replaced with.
 */
case class DefinitionRightRule( subProof: LKProof, aux: SequentIndex, main: HOLFormula )
    extends UnaryLKProof with CommonRule {
  override def name = "d:r"
  override def auxIndices = Seq( Seq( aux ) )
  override def mainFormulaSequent = Sequent() :+ main
}

object DefinitionRightRule extends ConvenienceConstructor( "DefinitionRightRule" ) {

  /**
   * Convenience constructor for d:r that, given an aux and main formula, will attempt to infer the main formula.
   *
   * @param subProof The subproof.
   * @param auxFormula The aux formula.
   * @param mainFormula The main formula.
   * @return
   */
  def apply( subProof: LKProof, auxFormula: HOLFormula, mainFormula: HOLFormula ): DefinitionRightRule = {
    val premise = subProof.endSequent
    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

    DefinitionRightRule( subProof, Suc( indices( 0 ) ), mainFormula )
  }
}

object DefinitionRule {
  def apply( subProof: LKProof, auxFormula: HOLFormula, mainFormula: HOLFormula, isSuc: Boolean ): LKProof =
    if ( isSuc )
      DefinitionRightRule( subProof, auxFormula, mainFormula )
    else
      DefinitionLeftRule( subProof, auxFormula, mainFormula )
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

  private def sequentToString( sequent: HOLSequent, highlightedFormulas: Seq[SequentIndex] ): String = {
    val stringSequent = sequent map { _.toString() }
    highlightedFormulas.foldLeft( stringSequent ) { ( acc, i ) =>
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
class ConvenienceConstructor( val longName: String ) {
  type IndexOrFormula = Either[SequentIndex, HOLFormula]

  /**
   * Create an LKRuleCreationException with a message starting with "Cannot create $longName: ..."
   *
   * @param text The rest of the message.
   * @return
   */
  protected def LKRuleCreationException( text: String ): LKRuleCreationException = new LKRuleCreationException( longName, text )

  def findIndicesOrFormulasInPremise( premise: HOLSequent )( antIndicesFormulas: Seq[IndexOrFormula], sucIndicesFormulas: Seq[IndexOrFormula] ): ( Seq[HOLFormula], Seq[Int], Seq[HOLFormula], Seq[Int] ) = {
    val antReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: antIndicesFormulas ) { ( acc, e ) =>
      e match {
        case Left( Ant( i ) ) => acc + i
        case Left( i: Suc )   => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
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

        case Left( i: Suc ) => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
      }
    }

    val sucReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: sucIndicesFormulas ) { ( acc, e ) =>
      e match {
        case Left( Suc( i ) ) => acc + i
        case Left( i: Ant )   => throw LKRuleCreationException( s"Index $i should be in the succedent." )
        case Right( _ )       => acc
      }
    }

    val suc = for ( e <- sucIndicesFormulas ) yield {
      e match {
        case Left( Suc( i: Int ) ) =>
          sucReservedIndices += i

          ( premise( Suc( i ) ), i )

        case Right( f: HOLFormula ) =>
          var i = premise.succedent.indexOf( f )

          while ( sucReservedIndices contains i )
            i = premise.succedent.indexOf( f, i + 1 )

          if ( i != -1 )
            sucReservedIndices += i

          ( f, i )

        case Left( i: Ant ) => throw LKRuleCreationException( s"Index $i should be in the succedent." )
      }
    }

    val ( antFormulas, antIndices ) = ant.unzip

    val ( sucFormulas, sucIndices ) = suc.unzip

    ( antFormulas, antIndices, sucFormulas, sucIndices )
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
   * Combines findIndicesOrFormulasInPremise and validateIndices. That is, it will return a pair of lists of indices and throw an exception if either
   * list contains a -1.
   *
   * @param premise The sequent in question.
   * @param antIndicesFormulas The list of indices or formulas in the antecedent.
   * @param sucIndicesFormulas The list of indices or formulas in the succedent.
   * @return
   */
  protected def findAndValidate( premise: HOLSequent )( antIndicesFormulas: Seq[IndexOrFormula], sucIndicesFormulas: Seq[IndexOrFormula] ): ( Seq[Int], Seq[Int] ) = {
    val ( antFormulas, antIndices, sucFormulas, sucIndices ) = findIndicesOrFormulasInPremise( premise )( antIndicesFormulas, sucIndicesFormulas )
    validateIndices( premise )( antFormulas, antIndices, sucFormulas, sucIndices )
    ( antIndices, sucIndices )
  }
}

class LKRuleCreationException( name: String, message: String ) extends Exception( s"Cannot create $name: " + message )
