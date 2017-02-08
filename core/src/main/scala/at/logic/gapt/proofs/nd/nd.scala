package at.logic.gapt.proofs.nd

import at.logic.gapt.expr.{freeVariables, _}
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

  def aux = Suc( 0 )

  def conjunction = premise( aux )

  def mainFormula = conjunction match {
    case And( leftConjunct, _ ) => leftConjunct
    case _                      => throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
  }

  override def auxIndices = Seq( Seq( aux ) )

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

  def aux = Suc( 0 )

  def conjunction = premise( aux )

  def mainFormula = conjunction match {
    case And( _, rightConjunct ) => rightConjunct
    case _                       => throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
  }

  override def auxIndices = Seq( Seq( aux ) )

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

  def aux = Suc( 0 )

  def leftConjunct = leftPremise( aux )
  def rightConjunct = rightPremise( aux )

  def mainFormula = And( leftConjunct, rightConjunct )

  def auxIndices = Seq( Seq( aux ), Seq( aux ) )

  override def name = "∧:i"

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

  def aux = Suc( 0 )

  def implication = leftPremise( aux )
  val antecedent = rightPremise( aux )

  def mainFormula = implication match {
    case Imp( `antecedent`, consequent ) => consequent
    case Imp( _, _ )                     => throw NDRuleCreationException( s"Proposed main formula $antecedent is not the antecedent of $implication." )
    case _                               => throw NDRuleCreationException( s"Proposed main formula $implication is not an implication." )
  }

  def auxIndices = Seq( Seq( aux ), Seq( aux ) )

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

  def impPremise = premise( aux )
  def impConclusion = premise( Suc( 0 ) )
  def mainFormula = Imp( impPremise, impConclusion )

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
   * Convenience constructor for →:i that, given a proposed main formula A → B, will attempt to create an inference with this main formula.
   *
   * @param subProof The subproof.
   * @param mainFormula The formula to be inferred. Must be of the form A → B.
   * @return
   */
  def apply( subProof: NDProof, mainFormula: HOLFormula ): ImpIntroRule = mainFormula match {
    case Imp( f, _ ) => apply( subProof, f )
    case _           => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not an implication." )
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

  def aux = Suc( 0 )

  val ( auxFormula, context ) = premise focus aux

  //eigenvariable condition
  if ( freeVariables( context ) contains eigenVariable )
    throw NDRuleCreationException( s"Eigenvariable condition is violated: $context contains $eigenVariable" )

  def subFormula = BetaReduction.betaNormalize( Substitution( eigenVariable, quantifiedVariable )( auxFormula ) )

  if ( BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) ) != auxFormula )
    throw NDRuleCreationException( s"Aux formula should be $subFormula[$quantifiedVariable\\$eigenVariable] = ${BetaReduction.betaNormalize( Substitution( quantifiedVariable, eigenVariable )( subFormula ) )}, but is $auxFormula." )

  def mainFormula = BetaReduction.betaNormalize( All( quantifiedVariable, subFormula ) )

  override def name = "∀:i"

  def auxIndices = Seq( Seq( aux ) )

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
  def apply(subProof: NDProof, mainFormula: HOLFormula, eigenVariable: Var): ForallIntroRule = mainFormula match {
    case All(v, subFormula) =>
      val auxFormula = Substitution(v, eigenVariable)(subFormula)

      val premise = subProof.endSequent

      val (_, indices) = findAndValidate(premise)(Seq(), Right(auxFormula))

      ForallIntroRule(subProof, eigenVariable, v)

    case _ => throw NDRuleCreationException(s"Proposed main formula $mainFormula is not universally quantified.")
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

  def aux = Suc( 0 )

  val mainFormula = Substitution( v, term )( A )

  override def name = "∀:l"

  def auxIndices = Seq( Seq( aux ) )

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
  def apply(subProof: NDProof, term: LambdaExpression): ForallElimRule = {
    val premise = subProof.endSequent

    val universal = premise( Suc( 0 ) )

    universal match {
      case All(v, subFormula) => ForallElimRule(subProof, subFormula, term, v)
      case _                  => throw NDRuleCreationException( s"Proposed main formula $universal is not universally quantified." )
    }
  }
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