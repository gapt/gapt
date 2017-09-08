package at.logic.gapt.proofsNew

import at.logic.gapt.expr.Formula
import at.logic.gapt.proofs.{ HOLSequent, SequentConnector, SequentIndex }

import scala.collection.immutable.IndexedSeq

trait SequentInference extends Inference[HOLSequent] {
  /**
   * A list of SequentIndices denoting the main formula(s) of the rule.
   */
  def mainIndices: Seq[SequentIndex]

  /**
   * The list of main formulas of the rule.
   */
  final def mainFormulas: Seq[Formula] = mainIndices map { conclusion( _ ) }

  /**
   * A list of lists of SequentIndices denoting the auxiliary formula(s) of the rule.
   * The first list contains the auxiliary formulas in the first premise and so on.
   */
  def auxIndices: Seq[Seq[SequentIndex]]

  /**
   * A list of lists containing the auxiliary formulas of the rule.
   * The first list constains the auxiliary formulas in the first premise and so on.
   */
  final def auxFormulas: Seq[Seq[Formula]] = for ( ( p, is ) <- premises zip auxIndices ) yield p( is )

  /**
   * A list of occurrence connectors, one for each immediate subproof.
   */
  def occConnectors: Seq[SequentConnector]
}

trait ContextInf extends SequentInference {
  protected def mainFormulaSequent: HOLSequent

  protected def contexts: Vector[HOLSequent] = for ( ( p, is ) <- premises zip auxIndices ) yield p.delete( is )

  override lazy val conclusion: HOLSequent = mainFormulaSequent.antecedent ++: contexts.flattenS :++ mainFormulaSequent.succedent

  override def mainIndices: Vector[SequentIndex] =
    ( mainFormulaSequent.antecedent.map( _ => true ) ++: contexts.flattenS.map( _ => false ) :++ mainFormulaSequent.succedent.map( _ => true ) ).indicesWhere( _ == true )

  private val contextIndices = for ( ( p, is ) <- premises zip auxIndices ) yield p.indicesSequent.delete( is )

  override def occConnectors: IndexedSeq[SequentConnector] = for ( i <- contextIndices.indices ) yield {
    val ( leftContexts, currentContext, rightContext ) = ( contextIndices.take( i ), contextIndices( i ), contextIndices.drop( i + 1 ) )
    val leftContextIndices = leftContexts.map( c => c.map( _ => Seq() ) )
    val currentContextIndices = currentContext.map( i => Seq( i ) )
    val rightContextIndices = rightContext.map( c => c.map( _ => Seq() ) )
    val auxIndicesAntecedent = mainFormulaSequent.antecedent.map( _ => auxIndices( i ) )
    val auxIndicesSuccedent = mainFormulaSequent.succedent.map( _ => auxIndices( i ) )
    SequentConnector( conclusion, premises( i ),
      auxIndicesAntecedent ++: ( leftContextIndices.flattenS ++ currentContextIndices ++ rightContextIndices.flattenS ) :++ auxIndicesSuccedent )
  }
}

private[proofsNew] trait SequentProofDefs {
  type SequentProof[Inf <: SequentInference] = DagProof[HOLSequent, Inf]
}
