package gapt.examples.sequence

import gapt.examples.implicationLeftMacro
import gapt.expr.formula.All
import gapt.expr.formula.Imp
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol.instantiate
import gapt.expr.subst.FOLSubstitution
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.LogicalAxiom

/**
 * Auxiliary structure to deal with axioms of the schema:
 * Forall variables cond1 -> cond2 -> ... -> condn -> consequence |- ...
 */
class AllQuantifiedConditionalAxiomHelper(
    variables: List[FOLVar], conditions: List[FOLAtom],
    consequence: FOLFormula ) {
  /**
   * Returns the full axiom
   */
  val getAxiom: FOLFormula =
    All.Block( variables, Imp.Block( conditions, consequence ) ).asInstanceOf[FOLFormula]

  /**
   * Use axiom with given expressions in proof.
   * Consequence of axiom must appear in current proof.
   * Instantiated conditions will of course remain in the antecedent of the returned proof
   */
  def apply( expressions: List[FOLTerm], p: LKProof ): LKProof = {
    assert( expressions.length == variables.length, "Number of expressions doesn't equal number of variables" )

    // construct implication with instantiated conditions and consequence
    val ( instantiated_conditions, instantiated_consequence ) =
      variables.indices.foldLeft( conditions -> consequence ) { ( acc, i ) =>
        val substitute = ( x: FOLFormula ) => FOLSubstitution( variables( i ), expressions( i ) )( x )
        ( acc._1.map( substitute ).asInstanceOf[List[FOLAtom]], substitute( acc._2 ) )
      }

    val p1 = apply_conditional_equality( instantiated_conditions, instantiated_consequence, p )

    // iteratively instantiate all-quantified variables with expression
    def instantiate_axiom( expressions: List[FOLTerm], axiom: FOLFormula, p: LKProof ): LKProof = {
      expressions match {
        case Nil => p
        case head :: tail =>
          val new_axiom = instantiate( axiom, head )
          val new_p = instantiate_axiom( tail, new_axiom, p )

          ForallLeftRule( new_p, axiom, head )

      }
    }

    val ax = getAxiom
    val p2 = instantiate_axiom( expressions, ax, p1 )

    ContractionLeftRule( p2, ax )
  }

  private def apply_conditional_equality( equalities: List[FOLAtom], result: FOLFormula, p: LKProof ): LKProof =
    implicationLeftMacro(
      equalities.map { LogicalAxiom },
      equalities.map { e => LogicalAxiom( e ) -> e }.toMap,
      result,
      p )
}
