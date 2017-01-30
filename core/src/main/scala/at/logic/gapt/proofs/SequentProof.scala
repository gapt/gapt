package at.logic.gapt.proofs

trait SequentProof[+Formula, This <: SequentProof[Formula, This]] extends DagProof[This] { self: This =>
  /**
   * A list of SequentIndices denoting the main formula(s) of the rule.
   */
  def mainIndices: Seq[SequentIndex]

  /**
   * The list of main formulas of the rule.
   */
  def mainFormulas: Seq[Formula] = mainIndices map { conclusion( _ ) }

  /**
   * A list of lists of SequentIndices denoting the auxiliary formula(s) of the rule.
   * The first list contains the auxiliary formulas in the first premise and so on.
   */
  def auxIndices: Seq[Seq[SequentIndex]]

  /**
   * The conclusion of the rule.
   */
  def conclusion: Sequent[Formula]

  /**
   * The upper sequents of the rule.
   */
  def premises: Seq[Sequent[Formula]] = immediateSubProofs map ( _.conclusion )

  /**
   * A list of lists containing the auxiliary formulas of the rule.
   * The first list constains the auxiliary formulas in the first premise and so on.
   */
  def auxFormulas: Seq[Seq[Formula]] = for ( ( p, is ) <- premises zip auxIndices ) yield p( is )

  /**
   * A list of occurrence connectors, one for each immediate subproof.
   */
  def occConnectors: Seq[SequentConnector]

  override protected def stepString( subProofLabels: Map[Any, String] ) =
    s"$conclusion    (${super.stepString( subProofLabels )})"
}

trait ContextRule[Formula, This <: SequentProof[Formula, This]] extends SequentProof[Formula, This] { self: This =>

  protected def formulasToBeDeleted = auxIndices

  protected def mainFormulaSequent: Sequent[Formula]

  protected def contexts = for ( ( p, is ) <- premises zip formulasToBeDeleted ) yield p.delete( is )

  override lazy val conclusion = mainFormulaSequent.antecedent ++: contexts.flattenS :++ mainFormulaSequent.succedent

  override def mainIndices = ( mainFormulaSequent.antecedent.map( _ => true ) ++: contexts.flattenS.map( _ => false ) :++ mainFormulaSequent.succedent.map( _ => true ) ).indicesWhere( _ == true )

  private val contextIndices = for ( ( p, is ) <- premises zip formulasToBeDeleted ) yield p.indicesSequent.delete( is )

  override def occConnectors = for ( i <- contextIndices.indices ) yield {
    val ( leftContexts, currentContext, rightContext ) = ( contextIndices.take( i ), contextIndices( i ), contextIndices.drop( i + 1 ) )
    val leftContextIndices = leftContexts.map( c => c.map( _ => Seq() ) )
    val currentContextIndices = currentContext.map( i => Seq( i ) )
    val rightContextIndices = rightContext.map( c => c.map( _ => Seq() ) )
    val auxIndicesAntecedent = mainFormulaSequent.antecedent.map( _ => formulasToBeDeleted( i ) )
    val auxIndicesSuccedent = mainFormulaSequent.succedent.map( _ => formulasToBeDeleted( i ) )
    SequentConnector( conclusion, premises( i ),
      auxIndicesAntecedent ++: ( leftContextIndices.flattenS ++ currentContextIndices ++ rightContextIndices.flattenS ) :++ auxIndicesSuccedent )
  }
}
