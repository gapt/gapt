package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.IndexOrFormula.{ IsFormula, IsIndex }
import at.logic.gapt.proofs._

import scala.collection.mutable

abstract class LKProof extends SequentProof[Formula, LKProof] {

  protected def LKRuleCreationException( message: String ): LKRuleCreationException =
    new LKRuleCreationException( longName, message )

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
  protected def validateIndices(
    premise:           HOLSequent,
    antecedentIndices: Seq[SequentIndex], succedentIndices: Seq[SequentIndex] ): Unit = {
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
  def getSequentConnector: SequentConnector = occConnectors.head

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

object BinaryLKProof {
  def unapply( p: BinaryLKProof ) = Some( p.endSequent, p.leftSubProof, p.rightSubProof )
}

trait CommonRule extends LKProof with ContextRule[Formula, LKProof]

/**
 * Use this trait for rules that use eigenvariables.
 *
 */
trait Eigenvariable {
  def eigenVariable: Var
}

case class ProofLink( referencedProof: Expr, referencedSequent: Sequent[Formula] ) extends InitialSequent {
  override def name = "link"
  override def conclusion = referencedSequent
}
object ProofLink {
  def apply( referencedProof: Expr )( implicit ctx: Context ): ProofLink =
    ProofLink( referencedProof, ctx.get[Context.ProofNames].lookup( referencedProof ).get )
}

/**
 * An LKProof consisting of a single sequent:
 * <pre>
 *     --------ax
 *      Γ :- Δ
 * </pre>
 */
abstract class InitialSequent extends LKProof {

  override def mainIndices = endSequent.indices

  override def auxIndices = Seq()

  override def immediateSubProofs = Seq()

  override def occConnectors = Seq()
}

object InitialSequent {
  def unapply( proof: InitialSequent ) = Some( proof.endSequent )
}

@deprecated( "Use ProofLink instead", since = "2.7" )
object TheoryAxiom {
  @deprecated( "Use ProofLink instead", since = "2.7" )
  def apply( conclusion: HOLSequent ) = ProofLink( foc"th", conclusion )
}

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
case class LogicalAxiom( A: Formula ) extends InitialSequent {
  override def name = "ax"
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
case class ReflexivityAxiom( s: Expr ) extends InitialSequent {
  override def name = "refl"
  override def conclusion = HOLSequent( Seq(), Seq( Eq( s, s ) ) )
  def mainFormula = Eq( s, s )
}

abstract class ContractionRule extends UnaryLKProof with CommonRule {
  def aux1: SequentIndex
  def aux2: SequentIndex

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  val mainFormula = premise( aux1 )
}

/**
 * An LKProof ending with a left contraction:
 * <pre>
 *         (π)
 *     A, A, Γ :- Δ
 *    --------------
 *      A, Γ :- Δ
 * </pre>
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionLeftRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends ContractionRule {

  validateIndices( premise, Seq( aux1, aux2 ), Seq() )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliary formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def name = "c:l"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ContractionLeftRule extends ConvenienceConstructor( "ContractionLeftRule" ) {
  /**
   * Convenience constructor for c:l that, given a formula to contract on the left,
   * will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: Formula ): ContractionLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( f, f ), Seq() )

    val p = ContractionLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ) )
    assert( p.mainFormula == f )
    p
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
 *
 * @param subProof The subproof π.
 * @param aux1 The index of one occurrence of A.
 * @param aux2 The index of the other occurrence of A.
 */
case class ContractionRightRule( subProof: LKProof, aux1: SequentIndex, aux2: SequentIndex ) extends ContractionRule {

  validateIndices( premise, Seq(), Seq( aux1, aux2 ) )

  if ( premise( aux1 ) != premise( aux2 ) )
    throw LKRuleCreationException( s"Auxiliary formulas ${premise( aux1 )} and ${premise( aux2 )} are not equal." )

  override def name = "c:r"

  override def mainFormulaSequent = Sequent() :+ mainFormula

}

object ContractionRightRule extends ConvenienceConstructor( "ContractionRightRule" ) {
  /**
   * Convenience constructor for c:r that, given a formula to contract on the right,
   * will automatically pick the first two occurrences of that formula.
   *
   * @param subProof The subproof π.
   * @param f The formula to contract.
   * @return
   */
  def apply( subProof: LKProof, f: Formula ): ContractionRightRule = {
    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( f, f ) )
    val p = ContractionRightRule( subProof, Suc( indices( 0 ) ), Suc( indices( 1 ) ) )
    assert( p.mainFormula == f )
    p
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
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningLeftRule( subProof: LKProof, formula: Formula )
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
 *
 * @param subProof The subproof π.
 * @param formula The formula A.
 */
case class WeakeningRightRule( subProof: LKProof, formula: Formula )
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
 *
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
    throw LKRuleCreationException(
      s"Auxiliary formulas are not the same:\n${leftPremise( aux1 )}\n${rightPremise( aux2 )}" )

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
  def apply( leftSubProof: LKProof, leftCutFormula: IndexOrFormula,
             rightSubProof: LKProof, rightCutFormula: IndexOrFormula ): CutRule = {
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
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, cutFormula: Formula ): CutRule = {
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
 *
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
  def apply( subProof: LKProof, auxFormula: Formula ): NegLeftRule = {
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
 *
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
  def apply( subProof: LKProof, auxFormula: Formula ): NegRightRule = {
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
 *
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
  def apply( subProof: LKProof, leftConjunct: IndexOrFormula, rightConjunct: IndexOrFormula ): AndLeftRule = {
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
  def apply( subProof: LKProof, mainFormula: Formula ): AndLeftRule = mainFormula match {
    case And( f, g ) =>
      val p = apply( subProof, f, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
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
 *
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
  def apply( leftSubProof: LKProof, leftConjunct: IndexOrFormula,
             rightSubProof: LKProof, rightConjunct: IndexOrFormula ): AndRightRule = {
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
  def apply( leftSubProof: LKProof, rightSubProof: LKProof,
             mainFormula: Formula ): AndRightRule = mainFormula match {
    case And( f, g ) =>
      val p = apply( leftSubProof, f, rightSubProof, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
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
 *
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
  def apply( leftSubProof: LKProof, leftDisjunct: IndexOrFormula,
             rightSubProof: LKProof, rightDisjunct: IndexOrFormula ): OrLeftRule = {
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
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: Formula ): OrLeftRule = mainFormula match {
    case Or( f, g ) =>
      val p = apply( leftSubProof, f, rightSubProof, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a disjunction." )
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
 *
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
   * Convenience constructor for ∨:r that, given a proposed main formula A ∨ B,
   * will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A ∨ B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): OrRightRule = mainFormula match {
    case Or( f, g ) =>
      val p = apply( subProof, f, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a disjunction." )
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
 *
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
  def apply( leftSubProof: LKProof, impPremise: IndexOrFormula,
             rightSubProof: LKProof, impConclusion: IndexOrFormula ): ImpLeftRule = {
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
  def apply( leftSubProof: LKProof, rightSubProof: LKProof, mainFormula: Formula ): ImpLeftRule = mainFormula match {
    case Imp( f, g ) =>
      val p = apply( leftSubProof, f, rightSubProof, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not a implication." )
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
 *
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
   * Convenience constructor for →:r that, given a proposed main formula A → B,
   * will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A → B.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ImpRightRule = mainFormula match {
    case Imp( f, g ) =>
      val p = apply( subProof, f, g )
      assert( p.mainFormula == mainFormula )
      p
    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not an implication." )
  }
}

trait SkolemQuantifierRule extends UnaryLKProof with CommonRule {
  def aux: SequentIndex
  def mainFormula: Formula
  def skolemTerm: Expr
  def skolemDef: Expr

  require( freeVariables( skolemDef ).isEmpty )

  val ( auxFormula, context ) = premise focus aux

  def quantifiedVariable: Var
  def subFormula: Formula

  val Apps( skolemConst: Const, skolemArgs ) = skolemTerm

  {
    val expectedMain = BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) )
    if ( expectedMain != mainFormula )
      throw LKRuleCreationException( s"Main formula should be $expectedMain, but is $mainFormula" )
  }

  {
    val expectedAux = BetaReduction.betaNormalize( instantiate( mainFormula, skolemTerm ) )
    if ( expectedAux != auxFormula )
      throw LKRuleCreationException(
        s"Aux formula should be $subFormula[$quantifiedVariable\\$skolemTerm] = $expectedAux, but is $auxFormula." )
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
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\t].
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ForallLeftRule( subProof: LKProof, aux: SequentIndex, A: Formula, term: Expr, v: Var )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq( aux ), Seq() )

  if ( premise( aux ) != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula = BetaReduction.betaNormalize( All( v, A ) )

  override def name = "∀:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ForallLeftRule extends ConvenienceConstructor( "ForallLeftRule" ) {
  /**
   * Convenience constructor for ∀:l that, given a main formula and a term,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A.
   * @param term A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, term: Expr ): ForallLeftRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )
        val i = premise.antecedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in antecedent of $premise." )

        val p = ForallLeftRule( subProof, Ant( i ), subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p

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
  def apply( subProof: LKProof, mainFormula: Formula ): ForallLeftRule = mainFormula match {
    case All( v, subFormula ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, term: Expr ): ForallLeftRule =
    mainFormula match {
      case All( v, subFormula ) =>
        val p = ForallLeftRule( subProof, aux, subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p
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
    throw LKRuleCreationException(
      s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = " +
        BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) +
        s", but is $auxFormula." )

  val mainFormula = BetaReduction.betaNormalize( All( quantifiedVariable, subFormula ) )

  override def name = "∀:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallRightRule extends ConvenienceConstructor( "ForallRightRule" ) {

  /**
   * Convenience constructor for ∀:r that, given a main formula and an eigenvariable,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, eigenVariable: Var ): ForallRightRule = {
    if ( freeVariables( mainFormula ) contains eigenVariable ) {
      throw LKRuleCreationException( s"Illegal main formula: Eigenvariable $eigenVariable is free in $mainFormula." )
    } else mainFormula match {
      case All( v, subFormula ) =>
        val auxFormula = Substitution( v, eigenVariable )( subFormula )

        val premise = subProof.endSequent

        val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

        val p = ForallRightRule( subProof, Suc( indices( 0 ) ), eigenVariable, v )
        assert( p.mainFormula == mainFormula )
        p

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
    }
  }

  /**
   * Convenience constructor for ∀:r that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∀x.A. The premise must contain A.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ForallRightRule = mainFormula match {
    case All( v, subFormula ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not universally quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, eigenVariable: Var ): ForallRightRule =
    mainFormula match {
      case All( v, _ ) =>
        val p = ForallRightRule( subProof, aux, eigenVariable, v )
        assert( p.mainFormula == mainFormula )
        p
    }
}

/**
 * An LKProof ending with a universal quantifier on the right:
 * <pre>
 *           (π)
 *      Γ :- Δ, A[x\s(...)]
 *     ---------------∀:r
 *      Γ :- Δ, ∀x.A
 * </pre>
 * This rule requires a Skolem function s(...)
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\α].
 * @param mainFormula The main formula A[x\s(...)]
 * @param skolemTerm The Skolem term s(...)
 * @param skolemDef The Skolem definition, see [[at.logic.gapt.expr.hol.SkolemFunctions]]
 */
case class ForallSkRightRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula,
                              skolemTerm: Expr, skolemDef: Expr )
  extends SkolemQuantifierRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  val All( quantifiedVariable, subFormula ) = mainFormula

  override def name = "∀sk:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ForallSkRightRule extends ConvenienceConstructor( "ForallSkRightRule" ) {

  /**
   * Convenience constructor for ∀sk:r that, given a Skolem term and Skolem definition,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @return
   */
  def apply( subProof: LKProof, skolemTerm: Expr, skolemDef: Expr ): ForallSkRightRule = {
    val Apps( _, skolemArgs ) = skolemTerm
    val mainFormula = BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) ).asInstanceOf[Formula]
    val auxFormula = instantiate( mainFormula, skolemTerm )

    val premise = subProof.endSequent

    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( auxFormula ) )

    ForallSkRightRule( subProof, Suc( indices( 0 ) ), mainFormula, skolemTerm, skolemDef )
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
    throw LKRuleCreationException(
      s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = " +
        BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) +
        s", but is $auxFormula." )

  val mainFormula = BetaReduction.betaNormalize( Ex( quantifiedVariable, subFormula ) )

  override def name = "∃:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ExistsLeftRule extends ConvenienceConstructor( "ExistsLeftRule" ) {

  /**
   * Convenience constructor for ∃:l that, given a main formula and an eigenvariable,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A.
   * @param eigenVariable A variable α such that A[α] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, eigenVariable: Var ): ExistsLeftRule = {
    if ( freeVariables( mainFormula ) contains eigenVariable ) {
      throw LKRuleCreationException( s"Illegal main formula: Eigenvariable $eigenVariable is free in $mainFormula." )
    } else mainFormula match {
      case Ex( v, subFormula ) =>
        val auxFormula = Substitution( v, eigenVariable )( subFormula )

        val premise = subProof.endSequent

        val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Seq() )
        val p = ExistsLeftRule( subProof, Ant( indices( 0 ) ), eigenVariable, v )
        assert( p.mainFormula == mainFormula )
        p

      case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
    }
  }

  /**
   * Convenience constructor for ∃:l that, given a main formula, will try to construct an inference with that formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A. The premise must contain A.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula ): ExistsLeftRule = mainFormula match {
    case Ex( v, subFormula ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, eigenVariable: Var ): ExistsLeftRule =
    mainFormula match {
      case Ex( v, _ ) => ExistsLeftRule( subProof, aux, eigenVariable, v )
    }
}

/**
 * An LKProof ending with an existential quantifier on the left:
 * <pre>
 *           (π)
 *      A[x\s(...)], Γ :- Δ
 *     --------------- ∃sk:l
 *       ∃x.A Γ :- Δ
 * </pre>
 * This rule requires a Skolem function s(...)
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\s(...)].
 * @param mainFormula The main formula A[x\s(...)]
 * @param skolemTerm The Skolem term s(...)
 * @param skolemDef The Skolem definition, see [[at.logic.gapt.expr.hol.SkolemFunctions]]
 */
case class ExistsSkLeftRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula,
                             skolemTerm: Expr, skolemDef: Expr )
  extends SkolemQuantifierRule {

  validateIndices( premise, Seq( aux ), Seq() )

  val Ex( quantifiedVariable, subFormula ) = mainFormula

  override def name = "∃sk:l"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object ExistsSkLeftRule extends ConvenienceConstructor( "ExistsSkLeftRule" ) {

  /**
   * Convenience constructor for ∃sk:l that, given a Skolem term and Skolem definition,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @return
   */
  def apply( subProof: LKProof, skolemTerm: Expr, skolemDef: Expr ): ExistsSkLeftRule = {
    val Apps( _, skolemArgs ) = skolemTerm
    val mainFormula = BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) ).asInstanceOf[Formula]
    val auxFormula = instantiate( mainFormula, skolemTerm )

    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( auxFormula ), Seq() )

    ExistsSkLeftRule( subProof, Ant( indices( 0 ) ), mainFormula, skolemTerm, skolemDef )
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
 *
 * @param subProof The proof π.
 * @param aux The index of A[x\t].
 * @param A The formula A.
 * @param term The term t.
 * @param v The variable x.
 */
case class ExistsRightRule( subProof: LKProof, aux: SequentIndex, A: Formula, term: Expr, v: Var )
  extends UnaryLKProof with CommonRule {

  validateIndices( premise, Seq(), Seq( aux ) )

  if ( premise( aux ) != BetaReduction.betaNormalize( Substitution( v, term )( A ) ) )
    throw LKRuleCreationException( s"Substituting $term for $v in $A does not result in ${premise( aux )}." )

  val mainFormula = BetaReduction.betaNormalize( Ex( v, A ) )

  override def name = "∃:r"

  def auxIndices = Seq( Seq( aux ) )

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object ExistsRightRule extends ConvenienceConstructor( "ExistsRightRule" ) {

  /**
   * Convenience constructor for ∃:r that, given a main formula and a term,
   * will try to construct an inference with that instantiation.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form ∃x.A.
   * @param term A term t such that A[t] occurs in the premise.
   * @return
   */
  def apply( subProof: LKProof, mainFormula: Formula, term: Expr ): ExistsRightRule = {
    val premise = subProof.endSequent

    mainFormula match {
      case Ex( v, subFormula ) =>
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, term )( subFormula ) )
        val i = premise.succedent indexOf auxFormula

        if ( i == -1 )
          throw LKRuleCreationException( s"Formula $auxFormula not found in succedent of $premise." )

        val p = ExistsRightRule( subProof, Suc( i ), subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p

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
  def apply( subProof: LKProof, mainFormula: Formula ): ExistsRightRule = mainFormula match {
    case Ex( v, subFormula ) =>
      val p = apply( subProof, mainFormula, v )
      assert( p.mainFormula == mainFormula )
      p

    case _ => throw LKRuleCreationException( s"Proposed main formula $mainFormula is not existentially quantified." )
  }

  def apply( subProof: LKProof, aux: SequentIndex, mainFormula: Formula, term: Expr ): ExistsRightRule =
    mainFormula match {
      case Ex( v, subFormula ) =>
        val p = ExistsRightRule( subProof, aux, subFormula, term, v )
        assert( p.mainFormula == mainFormula )
        p
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
  def replacementContext: Abs

  aux match {
    case Ant( _ ) => validateIndices( premise, Seq( eq, aux ), Seq() )
    case Suc( _ ) => validateIndices( premise, Seq( eq ), Seq( aux ) )
  }

  def equation = premise( eq )

  val auxFormula = premise( aux )

  val ( what, by, leftToRight ) = equation match {
    case Eq( s, t ) =>
      val insertS = BetaReduction.betaNormalize( App( replacementContext, s ) )
      val insertT = BetaReduction.betaNormalize( App( replacementContext, t ) )
      if ( insertS == auxFormula ) {
        ( s, t, true )
      } else if ( insertT == auxFormula ) {
        ( t, s, false )
      } else {
        throw LKRuleCreationException( s"Inserting $s into context yields $insertS; inserting" +
          s" $t yields $insertT. Neither is equal to $auxFormula." )
      }
    case _ => throw LKRuleCreationException( s"Formula $equation is not an equation." )
  }

  def mainFormula = BetaReduction.betaNormalize( App( replacementContext, by ) ).asInstanceOf[Formula]

  def auxIndices = Seq( Seq( eq, aux ) )

  override def formulasToBeDeleted = Seq( Seq( aux ) )

  def auxInConclusion = mainIndices.head
  def eqInConclusion = getSequentConnector.child( eq )

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
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
 */
case class EqualityLeftRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, replacementContext: Abs )
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
   * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula,
             replacementContext: Abs ): EqualityLeftRule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( eqFormula, auxFormula ), Seq() )

    EqualityLeftRule( subProof, Ant( indices( 0 ) ), Ant( indices( 1 ) ), replacementContext )

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
  def apply( subProof: LKProof, eq: IndexOrFormula, aux: IndexOrFormula, mainFormula: Formula ): EqualityLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( eq, aux ), Seq() )
    val ( eqFormula, auxFormula ) = ( premise( Ant( indices( 0 ) ) ), premise( Ant( indices( 1 ) ) ) )

    eqFormula match {
      case Eq( s, t ) =>
        if ( s == t && auxFormula == mainFormula ) {
          val repContext = replacementContext.abstractTerm( auxFormula )( s )

          val Abs( v, rest ) = repContext
          if ( auxFormula.find( s ).isEmpty )
            throw LKRuleCreationException( s"Eq is trivial, but term $s does not occur in $auxFormula." )

          EqualityLeftRule( subProof, eq, aux, repContext )

        } else if ( s == t && auxFormula != mainFormula ) {
          throw LKRuleCreationException(
            s"Eq is trivial, but aux formula $auxFormula and main formula $mainFormula differ." )

        } else if ( s != t && auxFormula == mainFormula ) {
          throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

        } else {
          val contextS = replacementContext( s.ty, auxFormula, auxFormula.find( s ) intersect mainFormula.find( t ) )
          val contextT = replacementContext( t.ty, auxFormula, auxFormula.find( t ) intersect mainFormula.find( s ) )

          val Abs( vS, restS ) = contextS
          val Abs( vT, restT ) = contextT

          if ( restS.find( vS ).isEmpty && restT.find( vT ).isEmpty )
            throw LKRuleCreationException( s"Neither $s nor $t found in formula $auxFormula." )

          val p = if ( BetaReduction.betaNormalize( App( contextS, t ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityLeftRule( subProof, eq, aux, contextS )
          } else if ( BetaReduction.betaNormalize( App( contextT, s ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityLeftRule( subProof, eq, aux, contextT )
          } else throw LKRuleCreationException( "Replacement in neither direction leads to proposed main formula." )

          assert( p.mainFormula == mainFormula )
          p
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
 * @param subProof The subproof π.
 * @param eq The index of s = t.
 * @param aux The index of the formula in which the replacement is to be performed.
 * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
 */
case class EqualityRightRule( subProof: LKProof, eq: SequentIndex, aux: SequentIndex, replacementContext: Abs )
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
   * @param replacementContext A term λx.A[x] that designates the positions to be replaced.
   * @return
   */
  def apply( subProof: LKProof, eqFormula: IndexOrFormula, auxFormula: IndexOrFormula,
             replacementContext: Abs ): EqualityRightRule = {
    val premise = subProof.endSequent

    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eqFormula ), Seq( auxFormula ) )

    EqualityRightRule( subProof, Ant( indicesAnt( 0 ) ), Suc( indicesSuc( 0 ) ), replacementContext )

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
  def apply( subProof: LKProof, eq: IndexOrFormula, aux: IndexOrFormula, mainFormula: Formula ): EqualityRightRule = {
    val premise = subProof.endSequent
    val ( indicesAnt, indicesSuc ) = findAndValidate( premise )( Seq( eq ), Seq( aux ) )
    val ( eqFormula, auxFormula ) = ( premise( Ant( indicesAnt( 0 ) ) ), premise( Suc( indicesSuc( 0 ) ) ) )

    eqFormula match {
      case Eq( s, t ) =>
        if ( s == t && auxFormula == mainFormula ) {
          val repContext = replacementContext.abstractTerm( auxFormula )( s )

          val Abs( v, rest ) = repContext
          if ( auxFormula.find( s ).isEmpty )
            throw LKRuleCreationException( s"Eq is trivial, but term $s does not occur in $auxFormula." )

          EqualityRightRule( subProof, eq, aux, repContext )

        } else if ( s == t && auxFormula != mainFormula ) {
          throw LKRuleCreationException( s"Eq is trivial, but aux formula $auxFormula and main formula $mainFormula." )

        } else if ( s != t && auxFormula == mainFormula ) {
          throw LKRuleCreationException( "Nontrivial equation, but aux and main formula are equal." )

        } else {
          val contextS = replacementContext( s.ty, auxFormula, auxFormula.find( s ) intersect mainFormula.find( t ) )
          val contextT = replacementContext( t.ty, auxFormula, auxFormula.find( t ) intersect mainFormula.find( s ) )

          val Abs( vS, restS ) = contextS
          val Abs( vT, restT ) = contextT

          if ( restS.find( vS ).isEmpty && restT.find( vT ).isEmpty )
            throw LKRuleCreationException( s"Neither $s nor $t found in formula $auxFormula." )

          val p = if ( BetaReduction.betaNormalize( App( contextS, t ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityRightRule( subProof, eq, aux, contextS )
          } else if ( BetaReduction.betaNormalize( App( contextT, s ) ) ==
            BetaReduction.betaNormalize( mainFormula ) ) {
            EqualityRightRule( subProof, eq, aux, contextT )
          } else throw LKRuleCreationException( "Replacement in neither direction leads to proposed main formula." )

          assert( p.mainFormula == mainFormula )
          p
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
 * The variables x,,i,, and y,,i,, are eigenvariables; x,,i,, are the eigenvariables of the
 * same type as the inductive data type, y,,i,, are the other arguments of the constructor c.
 * They can come in any order in the constructor.
 *
 * @param proof  The LKProof ending in the sequent of this case.
 * @param constructor  The constructor c of the inductive data type that we're considering.
 * @param hypotheses  Indices of F(x,,1,,), ..., F(x,,n,,)
 * @param eigenVars  The eigenvariables of this case: x,,1,,, ..., x,,n,,, y,,1,,, ..., y,,n,,
 *                   (these need to correspond to the order in c)
 * @param conclusion  Index of F(c(x,,1,,,...,x,,n,,,y,,1,,,...,y,,n,,))
 */
case class InductionCase( proof: LKProof, constructor: Const,
                          hypotheses: Seq[SequentIndex], eigenVars: Seq[Var],
                          conclusion: SequentIndex ) {
  val FunctionType( indTy, fieldTypes ) = constructor.ty
  require( fieldTypes == eigenVars.map( _.ty ) )

  val hypVars = eigenVars filter { _.ty == indTy }
  require( hypotheses.size == hypVars.size )

  hypotheses foreach { hyp =>
    require( hyp.isAnt && proof.endSequent.isDefinedAt( hyp ) )
  }

  val term = constructor( eigenVars: _* )

  require( conclusion.isSuc && proof.endSequent.isDefinedAt( conclusion ) )
}

/**
 * An LKProof ending with an induction rule:
 * <pre>
 *   (π,,1,,)   (π,,2,,)           (π,,n,,)
 * case 1      case 2     ...     case n
 * -------------------------------------(ind)
 * Γ :- Δ, F(t: indTy)
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
    require( c.proof.endSequent( c.conclusion ) == Substitution( quant -> c.term )( qfFormula ) )
  }
  for ( ( cas, ctx ) <- cases zip contexts )
    require( freeVariables( ctx.elements :+ formula ) intersect cas.eigenVars.toSet isEmpty )

  val mainFormula = BetaReduction.betaNormalize( formula( term ).asInstanceOf[Formula] )
  override protected def mainFormulaSequent = Sequent() :+ mainFormula
  override def auxIndices: Seq[Seq[SequentIndex]] = cases map { c => c.hypotheses :+ c.conclusion }
  override def immediateSubProofs: Seq[LKProof] = cases map { _.proof }

  private lazy val product = cases.flatMap { _.productIterator } :+ formula :+ term
  override def productArity = product.size
  override def productElement( n: Int ) = product( n )

  override def name = "ind"
}

abstract class DefinitionRule extends UnaryLKProof with CommonRule {
  def subProof: LKProof
  def aux: SequentIndex
  def auxFormula: Formula = premise( aux )
  def mainFormula: Formula
}

object DefinitionRule extends ConvenienceConstructor( "DefinitionRule" ) {
  def apply( subProof: LKProof, aux: SequentIndex, main: Formula ): LKProof =
    apply( subProof, aux, main, aux.polarity )
  def apply( subProof: LKProof, aux: IndexOrFormula, main: Formula, polarity: Polarity ): LKProof = polarity match {
    case Polarity.InSuccedent  => DefinitionRightRule( subProof, aux, main )
    case Polarity.InAntecedent => DefinitionLeftRule( subProof, aux, main )
  }
}

/**
 * An LKProof ending with a definition on the left.
 *
 * Introducing the definition c := φ on the left means replacing some occurrences of the expression φ by c in a
 * formula in the antecedent:
 *
 * <pre>
 *       (π)
 *    A[φ], Γ :- Δ
 *   -----------d:l
 *    A[c], Γ :- Δ
 * </pre>
 *
 * NB: LK proofs that contain this rule are not sound by construction, since it allows you to replace any formula
 * by any other formula. The soundness of such proofs can only be established with respect to a Context.
 * Use the `check` method on [[at.logic.gapt.proofs.Context]] to check whether the constructed proof is sound.
 *
 * @param subProof The proof π.
 * @param aux The index of A in the antecedent.
 * @param mainFormula The formula
 */
case class DefinitionLeftRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula ) extends DefinitionRule {
  override def name = "d:l"
  override def auxIndices = Seq( Seq( aux ) )
  override def mainFormulaSequent = mainFormula +: Sequent()
}

object DefinitionLeftRule extends ConvenienceConstructor( "DefinitionLeftRule" ) {

  /**
   * Convenience constructor for d:l.
   *
   * @param subProof The subproof.
   * @param aux The aux formula or its index.
   * @param mainFormula The main formula.
   */
  def apply( subProof: LKProof, aux: IndexOrFormula, mainFormula: Formula ): DefinitionLeftRule = {
    val premise = subProof.endSequent
    val ( indices, _ ) = findAndValidate( premise )( Seq( aux ), Seq() )

    DefinitionLeftRule( subProof, Ant( indices( 0 ) ), mainFormula )
  }
}

/**
 * An LKProof ending with a definition on the right.
 *
 * Introducing the definition c := φ on the right means replacing some occurrences of the expression φ by c in a
 * formula in the succedent:
 *
 * <pre>
 *       (π)
 *    Γ :- Δ, A[φ]
 *   -----------d:r
 *    Γ :- Δ, A[c]
 * </pre>
 *
 * NB: LK proofs that contain this rule are not sound by construction, since it allows you to replace any formula
 * by any other formula. The soundness of such proofs can only be established with respect to a Context.
 * Use the `check` method on [[at.logic.gapt.proofs.Context]] to check whether the constructed proof is sound.
 *
 * @param subProof The proof π.
 * @param aux The index of A in the succedent.
 * @param mainFormula The formula
 */
case class DefinitionRightRule( subProof: LKProof, aux: SequentIndex, mainFormula: Formula ) extends DefinitionRule {
  override def name = "d:r"
  override def auxIndices = Seq( Seq( aux ) )
  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object DefinitionRightRule extends ConvenienceConstructor( "DefinitionRightRule" ) {

  /**
   * Convenience constructor for d:r.
   *
   * @param subProof The subproof.
   * @param aux The aux formula or its index.
   * @param mainFormula The main formula.
   */
  def apply( subProof: LKProof, aux: IndexOrFormula, mainFormula: Formula ): DefinitionRightRule = {
    val premise = subProof.endSequent
    val ( _, indices ) = findAndValidate( premise )( Seq(), Seq( aux ) )

    DefinitionRightRule( subProof, Suc( indices( 0 ) ), mainFormula )
  }
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
  /**
   * Create an LKRuleCreationException with a message starting
   * with "Cannot create longName: ..."
   *
   * @param text The rest of the message.
   * @return
   */
  protected def LKRuleCreationException( text: String ): LKRuleCreationException =
    new LKRuleCreationException( longName, text )

  def findIndicesOrFormulasInPremise( premise: HOLSequent )(
    antIndicesFormulas: Seq[IndexOrFormula],
    sucIndicesFormulas: Seq[IndexOrFormula] ): ( Seq[Formula], Seq[Int], Seq[Formula], Seq[Int] ) = {
    val antReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: antIndicesFormulas ) { ( acc, e ) =>
      e match {
        case IsIndex( Ant( i ) ) => acc + i
        case IsIndex( i: Suc )   => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
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

        case IsIndex( i: Suc ) => throw LKRuleCreationException( s"Index $i should be in the antecedent." )
      }
    }

    val sucReservedIndices = ( scala.collection.mutable.HashSet.empty[Int] /: sucIndicesFormulas ) { ( acc, e ) =>
      e match {
        case IsIndex( Suc( i ) ) => acc + i
        case IsIndex( i: Ant )   => throw LKRuleCreationException( s"Index $i should be in the succedent." )
        case IsFormula( _ )      => acc
      }
    }

    val suc = for ( e <- sucIndicesFormulas ) yield {
      e match {
        case IsIndex( Suc( i: Int ) ) =>
          sucReservedIndices += i

          ( premise( Suc( i ) ), i )

        case IsFormula( f ) =>
          var i = premise.succedent.indexOf( f )

          while ( sucReservedIndices contains i )
            i = premise.succedent.indexOf( f, i + 1 )

          if ( i != -1 )
            sucReservedIndices += i

          ( f, i )

        case IsIndex( i: Ant ) => throw LKRuleCreationException( s"Index $i should be in the succedent." )
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
  protected def validateIndices( premise: HOLSequent )( antFormulas: Seq[Formula], antIndices: Seq[Int],
                                                        sucFormulas: Seq[Formula], sucIndices: Seq[Int] ) = {
    val antMap = scala.collection.mutable.HashMap.empty[Formula, Int]
    val sucMap = scala.collection.mutable.HashMap.empty[Formula, Int]

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
   * Combines findIndicesOrFormulasInPremise and validateIndices. That is, it will return a pair
   * of lists of indices and throw an exception if either list contains a -1.
   *
   * @param premise The sequent in question.
   * @param antIndicesFormulas The list of indices or formulas in the antecedent.
   * @param sucIndicesFormulas The list of indices or formulas in the succedent.
   * @return
   */
  protected def findAndValidate( premise: HOLSequent )(
    antIndicesFormulas: Seq[IndexOrFormula],
    sucIndicesFormulas: Seq[IndexOrFormula] ): ( Seq[Int], Seq[Int] ) = {
    val ( antFormulas, antIndices, sucFormulas, sucIndices ) =
      findIndicesOrFormulasInPremise( premise )( antIndicesFormulas, sucIndicesFormulas )
    validateIndices( premise )( antFormulas, antIndices, sucFormulas, sucIndices )
    ( antIndices, sucIndices )
  }
}

class LKRuleCreationException( name: String, message: String )
  extends Exception( s"Cannot create $name: " + message )
