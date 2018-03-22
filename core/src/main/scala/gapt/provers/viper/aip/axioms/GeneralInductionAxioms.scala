package gapt.provers.viper.aip.axioms

import gapt.expr.{ All, Formula, Var, freeVariables }
import gapt.proofs.{ Context, MutableContext, Sequent }
import gapt.provers.viper.aip._
import cats.instances.all._
import cats.syntax.all._

case class GeneralInductionAxioms(
    vsel: VariableSelector = allVariablesSelector( _ )( _ ),
    fsel: FormulaSelector  = firstFormulaSelector( _ ) ) extends AxiomFactory {

  def forAllVariables = copy( vsel = allVariablesSelector( _ )( _ ) )

  def forVariables( variables: List[Var] ) = copy( vsel = ( _, _ ) => variables )

  def forVariables( variables: Var* ) = copy( vsel = ( _, _ ) => variables.toList )

  def forLabel( label: String ) = copy( fsel = findFormula( _, label ) )

  def forFormula( formula: Formula ) = copy( fsel = _ => Right( formula ) )

  /**
   * Generates independent induction axioms for the given sequent.
   *
   * @param sequent The sequent for which the induction axioms are generated.
   * @return Either a list of induction axioms, or a list of error-messages if the axioms could not be created
   */
  override def apply( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): ThrowsError[List[Axiom]] = {
    for {
      formula <- fsel( sequent )
      variables = vsel( formula, ctx )
      axioms <- variables.traverse[ThrowsError, Axiom] {
        variable => inductionAxiom( variables, variable, formula )
      }
    } yield axioms
  }

  private def inductionAxiom(
    inductionVariables: List[Var], variable: Var, formula: Formula )( implicit ctx: MutableContext ): ThrowsError[Axiom] = {
    val closedVariables = inductionVariables filter { _ != variable }
    val inductionFormula = All.Block( closedVariables, formula )
    StandardInductionAxioms( variable, inductionFormula ) map { axiom =>
      new Axiom {
        val formula = axiom.formula
        def proof = { axiom.proof }
      }
    }
  }
}
