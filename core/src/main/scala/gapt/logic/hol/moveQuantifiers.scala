package gapt.logic.hol

import gapt.expr.Var
import gapt.expr.formula._
import gapt.expr.subst.Substitution
import gapt.expr.util.{freeVariables, rename, variables}

object moveQuantifiers {

  /**
   * Moves all quantifiers of the given type (increases the scope) as far as possible by applying
   * the following equivalences in the right to left direction:
   *
   * - ∃z (α[z/x] ∨ β[z/y]) <-> (∃x α) ∨ (∃y β) where z neither occurs in α nor in β,
   * - ∀z (α[z/x] ∧ β[z/y]) <-> (∀x α) ∧ (∀y β) where z neither occurs in α nor in β,
   * - Qx (α C β) <-> (Qx α) C β where Q is a quantifier, C ∈ {∧,∨} and x does not occur in β,
   * - Qx (β C α) <-> β C (Qx α) where Q is a quantifier, C ∈ {∧,∨} and x does not occur in β.
   *
   * @param quantifier the type of quantifier to move up
   * @param formula formula in which to move the quantifier up
   * @return result of applying the above equivalences in the right to left equivalences
   *         as often as possible to the input formula
   */
  def up(quantifier: QuantifierHelper, formula: Formula): Formula = formula match {
    case AndOr(quantifier(variableAlpha, alpha), quantifier(variableBeta, beta), connective) if quantifier isCompatibleWith connective =>
      fuseQuantifierOverConnective(quantifier, connective, List(variableAlpha -> alpha, variableBeta -> beta))

    case AndOr(quantifier(variable, beta), alpha, connective) =>
      fuseQuantifierOverConnective(quantifier, connective, List(variable -> beta, variable -> alpha))

    case AndOr(alpha, quantifier(variable, beta), connective) =>
      fuseQuantifierOverConnective(quantifier, connective, List(variable -> alpha, variable -> beta))

    case Quant(variable, alpha, pol) =>
      Quant(variable, up(quantifier, alpha), pol)

    case AndOr(alpha, beta, connective) =>
      val movedAlpha = up(quantifier, alpha)
      val movedBeta = up(quantifier, beta)
      if (movedAlpha != alpha || movedBeta != beta)
        up(quantifier, connective(movedAlpha, movedBeta))
      else
        formula

    case Neg(innerFormula) => Neg(up(quantifier, innerFormula))

    case _ => formula
  }

  /**
   * Moves all quantifiers of the given type down (decreases the scope) as far as possible by applying
   * the following equivalences in the left to right direction:
   *
   * - ∃x (α ∨ β) <-> (∃x α) ∨ (∃x β),
   * - ∀x (α ∧ β) <-> (∀x α) ∧ (∀x β),
   * - Qx (α C β) <-> (Qx α) C β where Q is a quantifier, C ∈ {∧, ∨} and x does not occur in β,
   * - Qx (β C α) <-> β C (Qx α) where Q is a quantifier, C ∈ {∧, ∨} and x does not occur in β.
   *
   * Moving stops when function encounters
   *
   * @param quantifier the type of quantifier to move down
   * @param formula formula in which to move the quantifier down
   * @return result of applying the above equivalences in the left to right direction
   *         as often as possible to the input formula
   */
  def down(quantifier: QuantifierHelper, formula: Formula): Formula = formula match {
    case quantifier(variable, AndOr(alpha, beta, connective)) if quantifier isCompatibleWith connective =>
      connective(
        down(quantifier, quantifier(variable, alpha)),
        down(quantifier, quantifier(variable, beta))
      )

    case quantifier(variable, AndOr(alpha, beta, connective)) if variable isNotFreeIn alpha =>
      connective(
        down(quantifier, alpha),
        down(quantifier, quantifier(variable, beta))
      )

    case quantifier(variable, AndOr(beta, alpha, connective)) if variable isNotFreeIn alpha =>
      connective(
        down(quantifier, quantifier(variable, beta)),
        down(quantifier, alpha)
      )

    case Quant(variable, alpha, pol) =>
      Quant(variable, down(quantifier, alpha), pol)

    case AndOr(alpha, beta, connective) =>
      connective(
        down(quantifier, alpha),
        down(quantifier, beta)
      )

    case Neg(innerFormula) => Neg(down(quantifier, innerFormula))

    case _ => formula
  }

  private implicit class QuantifierConnectiveHelper(quantifierHelper: QuantifierHelper) {
    def isCompatibleWith(connective: MonoidalBinaryPropConnectiveHelper): Boolean = quantifierHelper match {
      case Ex  => connective == Or
      case All => connective == And
      case _   => false
    }
  }

  private implicit class VariableHelper(variable: Var) {
    def isNotFreeIn(formula: Formula): Boolean = !freeVariables(formula).contains(variable)
  }

  private def fuseQuantifierOverConnective(quantifier: QuantifierHelper, connective: MonoidalBinaryPropConnectiveHelper, variablesInFormulas: Seq[(Var, Formula)]): Formula = {
    val (newVariable, substitutedFormulas) = replaceVariablesWithNewVariable(variablesInFormulas)
    quantifier(newVariable, up(quantifier, connective(substitutedFormulas)))
  }

  private def replaceVariablesWithNewVariable[T](variablesInFormulas: Seq[(Var, Formula)]): (Var, Seq[Formula]) =
    variablesInFormulas match {
      case (headVariable: Var, _) +: _ =>
        val blackListVariables = variablesInFormulas.flatMap(x => variables(x._2))
        val newVariable = rename(headVariable, blackListVariables)
        val variableSubstitution = Substitution(variablesInFormulas.map {
          case (variable, _) => variable -> newVariable
        })
        val substitutedFormulas = variablesInFormulas.map {
          case (_, formula) => variableSubstitution(formula)
        }
        (newVariable, substitutedFormulas)
    }
}
