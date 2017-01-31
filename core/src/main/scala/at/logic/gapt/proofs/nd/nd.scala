package at.logic.gapt.proofs.nd

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.AndLeftRule

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
   * @param succedentIndex Indices that should be in the succedent.
   */
  protected def validateIndices( premise: HOLSequent, antecedentIndices: Seq[SequentIndex], succedentIndex: SequentIndex ): Unit = {
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

    succedentIndex match {
      case Suc( _ ) =>

        if ( !premise.isDefinedAt( succedentIndex ) )
          throw NDRuleCreationException( s"Sequent $premise is not defined at index $succedentIndex." )

      case Ant( _ ) => throw NDRuleCreationException( s"Index $succedentIndex should be in the succedent." )
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

object UnaryLKProof {
  def unapply( p: UnaryNDProof ) = Some( p.endSequent, p.subProof )
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
 * An LKProof consisting of a single sequent:
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
  override def name = "ax"
  override def conclusion = NDSequent( Seq( A ), A )
  def mainFormula = A
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
case class AndElim1Rule( subProof: NDProof, aux1: SequentIndex, aux2: SequentIndex )
  extends UnaryNDProof with CommonRule {

  validateIndices( premise, Seq( aux1, aux2 ), aux1 )

  val leftConjunct = premise( aux1 )
  val rightConjunct = premise( aux2 )
  val mainFormula = And( leftConjunct, rightConjunct )

  override def auxIndices = Seq( Seq( aux1, aux2 ) )

  override def name = "∧:e1"

  override def mainFormulaSequent = mainFormula +: Sequent()
}

object AndElim1Rule extends ConvenienceConstructor( "AndElim1Rule" ) {

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
  def apply( subProof: NDProof, leftConjunct: Either[SequentIndex, HOLFormula], rightConjunct: Either[SequentIndex, HOLFormula] ): AndElim1Rule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( leftConjunct, rightConjunct ), leftConjunct )

    AndElim1Rule( subProof, Suc( indices( 0 ) ), Suc( indices( 1 ) ) )
  }

  /**
    * Convenience constructor for ∧:l.
    * Given a proposed main formula A ∧ B, it will attempt to create an inference with this main formula.
    *
    * @param subProof The subproof.
    * @param mainFormula The main formula to be inferred. Must be of the form A ∧ B.
    * @return
    */
  def apply( subProof: NDProof, mainFormula: HOLFormula ): AndElim1Rule = mainFormula match {
    case And( f, g ) => apply( subProof, Right(f), Right(g) )
    case _           => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
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
case class AndIntroRule( leftSubProof: NDProof, aux1: SequentIndex, rightSubProof: NDProof, aux2: SequentIndex )
  extends BinaryNDProof with CommonRule {

  validateIndices( leftPremise, Seq(), aux1 )
  validateIndices( rightPremise, Seq(), aux2 )

  val leftConjunct = leftPremise( aux1 )
  val rightConjunct = rightPremise( aux2 )

  val mainFormula = And( leftConjunct, rightConjunct )

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "∧:i"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object AndIntroRule extends ConvenienceConstructor( "AndIntroRule" ) {

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
  def apply( leftSubProof: NDProof, leftConjunct: IndexOrFormula, rightSubProof: NDProof, rightConjunct: IndexOrFormula ): AndIntroRule = {
    val ( leftPremise, rightPremise ) = ( leftSubProof.endSequent, rightSubProof.endSequent )

    val ( _, leftIndex ) = findAndValidate( leftPremise )( Seq(), leftConjunct )
    val ( _, rightIndex ) = findAndValidate( rightPremise )( Seq(), rightConjunct )

    new AndIntroRule( leftSubProof, Suc( leftIndex ), rightSubProof, Suc( rightIndex ) )
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
  def apply( leftSubProof: NDProof, rightSubProof: NDProof, mainFormula: HOLFormula ): AndIntroRule = mainFormula match {
    case And( f, g ) => apply( leftSubProof, Right(f), rightSubProof, Right(g) )
    case _           => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
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
    * @param sucFormula The list of formulas in the succedent.
    * @param sucIndex The list indices corresponding to sucFormulas.
    * @return
    */
  protected def validateIndices( premise: HOLSequent )( antFormulas: Seq[HOLFormula], antIndices: Seq[Int], sucFormula: HOLFormula, sucIndex: Int ) = {
    val antMap = scala.collection.mutable.HashMap.empty[HOLFormula, Int]

    for ( ( f, i ) <- antFormulas zip antIndices ) {
      val count = antMap.getOrElse( f, 0 )

      if ( i == -1 )
        throw NDRuleCreationException( s"Formula $f only found $count times in antecedent of $premise." )

      antMap += f -> ( count + 1 )
    }

    if ( sucIndex == -1 )
      throw NDRuleCreationException( s"Formula $sucFormula only found with index $sucIndex in succedent of $premise." )
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
    validateIndices( premise )( antFormulas, antIndices, sucFormula, sucIndex )
    ( antIndices, sucIndex )
  }
}

class NDRuleCreationException( name: String, message: String ) extends Exception( s"Cannot create $name: " + message )