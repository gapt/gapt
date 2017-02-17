package at.logic.gapt.provers.viper.aip.axioms
import at.logic.gapt.expr.Var
import at.logic.gapt.proofs.Context
import at.logic.gapt.provers.viper.aip.{ LabelledSequent, ThrowsError, findFormula }
import cats.syntax.all._
import cats.instances.all._

case class StandardInductionAxioms(
    variableSelector: VariableSelector = allVariablesSelector( _ )( _ ),
    formulaSelector:  FormulaSelector  = firstFormulaSelector( _ )
) extends AxiomFactory {

  def forAllVariables = copy( variableSelector = allVariablesSelector( _ )( _ ) )

  def forLabel( label: String ) = copy( formulaSelector = findFormula( _, label ) )

  def forVariables( variables: Var* ) = copy( variableSelector = ( _, _ ) => variables.toList )

  /**
   * Computes induction axioms for a given sequent.
   *
   * @param sequent The sequent for which the axioms are generated.
   * @param ctx     Defines inductive types etc.
   * @return Either a list of induction axioms or a non empty list of strings describing the why induction axioms
   *         could not be generated.
   */
  override def apply( sequent: LabelledSequent )( implicit ctx: Context ): ThrowsError[List[Axiom]] = {
    for {
      formula <- formulaSelector( sequent )
      variables = variableSelector( formula, ctx )
      axioms <- variables.traverse[ThrowsError, List[Axiom]] {
        v => SequentialInductionAxioms( ( _, _ ) => v :: Nil, formulaSelector )( sequent )
      }
    } yield axioms.flatten
  }
}
