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

trait CommonRule extends NDProof with ContextRule[HOLFormula, NDProof]

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

  val aux = Suc( 0 )

  val conjunction = premise( aux )

  val mainFormula = conjunction match {
    case And( leftConjunct, _ ) => leftConjunct
    case _ => throw new Exception("")
  }

  override def auxIndices = Seq( Seq( aux ) )

  override def name = "∧:e1"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object AndElim1Rule extends ConvenienceConstructor( "AndElim1Rule" ) {

  /*
  /**
    * Convenience constructor for ∧:l.
    * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
    * will attempt to find an appropriate index on its own.
    *
    * @param subProof The subproof.
    * @param conjunct Index of the left conjunct or the conjunct itself.
    * @return
    */
  def apply( subProof: NDProof, conjunct: HOLFormula ): AndElim1Rule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( Right(conjunct) ), Right(conjunct) )

    AndElim1Rule( subProof )
  }
  */

  /**
    * Convenience constructor for ∧:e1.
    * Given a proposed main formula A, it will attempt to create an inference with this main formula.
    *
    * @param subProof The subproof.
    * @param mainFormula The main formula to be inferred.
    * @return
    */
  def apply( subProof: NDProof, mainFormula: HOLFormula ): AndElim1Rule = mainFormula match {
    case f : HOLFormula => apply( subProof, f )
    case _ => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
  }
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

  val aux = Suc( 0 )

  val conjunction = premise( aux )

  val mainFormula = conjunction match {
    case And( _, rightConjunct ) => rightConjunct
    case _ => throw NDRuleCreationException( s"Proposed main formula $conjunction is not a conjunction." )
  }

  override def auxIndices = Seq( Seq( aux ) )

  override def name = "∧:e2"

  override def mainFormulaSequent = Sequent() :+ mainFormula
}

object AndElim2Rule extends ConvenienceConstructor( "AndElim2Rule" ) {

  /*
  /**
    * Convenience constructor for ∧:e2.
    * Each of the aux formulas can be given as an index or a formula. If it is given as a formula, the constructor
    * will attempt to find an appropriate index on its own.
    *
    * @param subProof The subproof.
    * @param conjunct Index of the left conjunct or the conjunct itself.
    * @return
    */
  def apply( subProof: NDProof, conjunct: HOLFormula ): AndElim2Rule = {
    val premise = subProof.endSequent

    val ( indices, _ ) = findAndValidate( premise )( Seq( Right(conjunct) ), Right(conjunct) )

    AndElim2Rule( subProof )
  }
  */

  /**
    * Convenience constructor for ∧:e2.
    * Given a proposed main formula A, it will attempt to create an inference with this main formula.
    *
    * @param subProof The subproof.
    * @param mainFormula The main formula to be inferred.
    * @return
    */
  def apply( subProof: NDProof, mainFormula: HOLFormula ): AndElim2Rule = mainFormula match {
    case f : HOLFormula => apply( subProof, f )
    case _ => throw NDRuleCreationException( s"." )
  }
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

  val aux = Suc( 0 )

  val leftConjunct = leftPremise( aux )
  val rightConjunct = rightPremise( aux )

  val mainFormula = And( leftConjunct, rightConjunct )

  def auxIndices = Seq( Seq( aux ), Seq( aux ) )

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

    new AndIntroRule( leftSubProof, rightSubProof )
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
    case And( f, g ) => apply( leftSubProof, rightSubProof )
    case _           => throw NDRuleCreationException( s"Proposed main formula $mainFormula is not a conjunction." )
  }
}

/**
  * An NDProof ending with elimination of an implication:
  * <pre>
  *     (π1)       (π2)
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

  val aux1 = Suc( 0 )
  val aux2 = Suc( 0 )

  val implication = leftPremise( aux1 )
  val antecedent = rightPremise( aux2 )

  val mainFormula = implication match {
    case Imp( antecedent, consequent ) => consequent
    case Imp( _,_ ) => throw NDRuleCreationException( s"Proposed main formula $antecedent is not the antecedent of $implication." )
    case _ => throw NDRuleCreationException( s"Proposed main formula $implication is not an implication." )
  }

  def auxIndices = Seq( Seq( aux1 ), Seq( aux2 ) )

  override def name = "\u2283:i"

  override def mainFormulaSequent =  Sequent() :+ mainFormula

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