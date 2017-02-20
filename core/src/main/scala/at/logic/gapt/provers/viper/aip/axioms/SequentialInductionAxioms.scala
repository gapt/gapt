package at.logic.gapt.provers.viper.aip.axioms

import at.logic.gapt.expr.{ All, HOLFormula, Var, freeVariables, Const => Con }
import at.logic.gapt.proofs.gaptic.{ ProofState, allR, insert, repeat }
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.aip.{ ThrowsError, findFormula }
import cats.instances.all._
import cats.syntax.all._

/**
 * Generates sequential induction axioms.
 *
 * @param vsel The variables for which an induction axiom is generated.
 * @param fsel The formula of a sequent for which induction axioms are generated.
 */
case class SequentialInductionAxioms(
    vsel: VariableSelector = allVariablesSelector( _ )( _ ),
    fsel: FormulaSelector  = firstFormulaSelector( _ )
) extends AxiomFactory {

  def forAllVariables = copy( vsel = allVariablesSelector( _ )( _ ) )

  def forVariables( variables: List[Var] ) = copy( vsel = ( _, _ ) => variables )

  def forVariables( variables: Var* ) = copy( vsel = ( _, _ ) => variables.toList )

  def forLabel( label: String ) = copy( fsel = findFormula( _, label ) )

  def forFormula( formula: HOLFormula ) = copy( fsel = _ => Right( formula ) )

  /**
   * Computes sequential induction axioms for a sequent.
   *
   * @param sequent The sequent for which the axioms are generated.
   * @param ctx     The context defining types, constants, etc.
   * @return Failure if the one of the given variables is not of inductive type.
   *         Otherwise a list of induction axioms of the form:
   *         ∀A∀{X < x}( IC(x,c,,1,,) ∧ ... ∧ IC(x,c,,l,,) -> ∀x∀{X > x}∀{X'}F ),
   *         where
   *         the input variables are X
   *         the input formula is of the form F' = ∀{X U X'}F
   *         FV(F') = A
   *         x in X
   *         {X < x} and {X > x} are subsets of X containing all variables with index smaller/greater than the index of x.
   */
  override def apply( sequent: Sequent[( String, HOLFormula )] )( implicit ctx: Context ): ThrowsError[List[Axiom]] = {
    for {
      formula <- fsel( sequent )
      variables = vsel( formula, ctx )
      axioms <- variables.traverse[ThrowsError, Axiom] { v: Var => inductionAxiom( variables, v, formula ) }
    } yield axioms
  }

  private def inductionAxiom( variables: List[Var], variable: Var, formula: HOLFormula )( implicit ctx: Context ): ThrowsError[Axiom] = {
    val ( outerVariables, _ :: innerVariables ) = variables span { _ != variable }
    val inductionFormula = All.Block( innerVariables, inductionQuantifierForm( variables, formula ) )

    StandardInductionAxioms( variable, inductionFormula ).map { axiom =>
      new Axiom {
        val formula = All.Block( outerVariables, axiom.formula )
        def proof = {
          ProofState( Sequent() :+ formula ) + repeat( allR ) + insert( axiom.proof ) result
        }
      }
    }
  }

  private def inductionQuantifierForm( inductionVariables: List[Var], formula: HOLFormula ): HOLFormula = {
    val All.Block( _, matrix ) = formula
    val quantifierPrefix = freeVariables( matrix ).diff( freeVariables( formula ) ).diff( inductionVariables.toSet ).toSeq

    All.Block( quantifierPrefix, matrix )
  }
}
