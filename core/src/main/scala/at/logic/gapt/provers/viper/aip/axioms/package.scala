package at.logic.gapt.provers.viper.aip

import at.logic.gapt.expr.{ All, And, Const => Con, FunctionType, HOLFormula, Substitution, Var, freeVariables, rename }
import at.logic.gapt.proofs.{ Context, Sequent }

package object axioms {

  type VariableSelector = ( HOLFormula, Context ) => List[Var]
  type FormulaSelector = Sequent[( String, HOLFormula )] => ThrowsError[HOLFormula]

  /**
   * Selects variables of inductive types.
   *
   * @param formula The formula from which the variables are selected.
   * @param ctx The context which fixes constants, types, etc.
   * @return A list of all free inductive variables and all universally quantified inductive variables
   *         that are bound in the universal quantifier prefix of the given formula.
   */
  def allVariablesSelector( formula: HOLFormula )( implicit ctx: Context ): List[Var] = {
    val All.Block( _, f ) = formula
    freeVariables( f ).filter( {
      hasInductiveType( _ )
    } ).toList
  }

  /**
   * Selects the first formula in the succedent of a sequent.
   * @param sequent The sequent from which the formula is selected.
   * @return The formula at the first position of the sequent's succedent.
   */
  def firstFormulaSelector( sequent: Sequent[( String, HOLFormula )] ): ThrowsError[HOLFormula] =
    sequent.succedent match {
      case ( _, f ) +: _ => Right( f )
      case _             => Left( "Succedent is empty" )
    }

  /**
   * Constructs a standard induction axiom.
   *
   * @param inductionVariable The variable on which the induction is carried out.
   * @param formula The formula for which the induction axiom is to be generated
   * @param constructors The constructors of the induction variable.
   * @param ctx The context which fixes constants, types, etc.
   * @return An induction axiom representing an induction on the specified variable and formula with one induction
   *         case for each of the constructors.
   */
  def inductionAxiom( inductionVariable: Var, formula: HOLFormula, constructors: Seq[Con] )( implicit ctx: Context ) =
    And( constructors map { inductionCase( inductionVariable, formula, _ ) } ) -->
      All( inductionVariable, formula )

  /**
   * Constructs a formula representing an inductive case.
   *
   * @param inductionVariable The variable on which the induction is carried out.
   * @param formula The induction formula.
   * @param constructor The constructor associated with the induction case.
   * @return A formula representing the inductive case for the given constructor for an induction on the specified
   *         formula and variable.
   */
  def inductionCase( inductionVariable: Var, formula: HOLFormula, constructor: Con ): HOLFormula = {
    val ( primaryVariables, secondaryVariables, caseConclusion ) =
      inductionCaseConclusion( inductionVariable, constructor, formula )
    val caseHypotheses = primaryVariables.map { pv => Substitution( inductionVariable -> pv )( formula ) }

    All.Block( primaryVariables, And( caseHypotheses ) --> All.Block( secondaryVariables, caseConclusion ) )
  }

  /**
   * Constructs the conclusion of an inductive case.
   *
   * @param freeVariable The free variable which is to be replaced by the given constructor.
   * @param constructor The constructor to be inserted at all occurrences of the specified freeVariable.
   * @param formula The formula in which the substitution is to be carried out.
   * @return A three tuple whose first component contains a list of all newly introduced free variables that
   *         are of the same type as the type to which the constructor belongs, the second component contains
   *         a list of all newly introduced variables that are of a different type than the constructor's type,
   *         the third component contains the result of the substitution.
   */
  def inductionCaseConclusion(
    freeVariable: Var, constructor: Con, formula: HOLFormula
  ): ( List[Var], List[Var], HOLFormula ) = {
    val FunctionType( _, argumentTypes ) = constructor.exptype
    val nameGenerator = rename.awayFrom( freeVariables( formula ) )
    val newVariables = argumentTypes map {
      argumentType =>
        nameGenerator.fresh(
          if ( argumentType == freeVariable.exptype )
            freeVariable
          else
            Var( "x", argumentType )
        )
    }
    val ( primaryVariables, secondaryVariables ) = newVariables partition {
      _.exptype == freeVariable.exptype
    }
    ( primaryVariables, secondaryVariables, Substitution( freeVariable -> constructor( newVariables: _* ) )( formula ) )
  }
}
