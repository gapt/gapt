package at.logic.gapt.provers.viper.aip

import at.logic.gapt.expr.{ All, HOLFormula, Var, freeVariables }
import at.logic.gapt.proofs.{ Context, Sequent }

package object axioms {

  type VariableSelector = ( HOLFormula, Context ) => List[Var]
  type FormulaSelector = Sequent[( String, HOLFormula )] => ThrowsError[HOLFormula]

  def allVariablesSelector( formula: HOLFormula )( implicit ctx: Context ): List[Var] = {
    val All.Block( _, f ) = formula
    freeVariables( f ).filter( {
      hasInductiveType( _ )
    } ).toList
  }

  def firstFormulaSelector( sequent: Sequent[( String, HOLFormula )] ): ThrowsError[HOLFormula] =
    sequent.succedent match {
      case ( _, f ) +: _ => Right( f )
      case _             => Left( "Succedent is empty" )
    }
}
