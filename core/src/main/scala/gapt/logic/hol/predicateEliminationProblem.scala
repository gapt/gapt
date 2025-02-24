package gapt.logic.hol

import gapt.expr.formula.Formula
import gapt.expr.Var
import gapt.expr.formula.Ex
import gapt.proofs.HOLClause
import gapt.expr.formula.And
import gapt.expr.formula.All
import gapt.proofs.RichFormulaSequent
import gapt.expr.Expr
import gapt.expr.formula.fol.FOLVar
import gapt.expr.util.freeVariables
import gapt.expr.formula.hol.freeHOVariables
import gapt.expr.subst.Substitution
import gapt.expr.Const
import gapt.proofs.Sequent
import gapt.proofs.resolution.structuralCNF
import gapt.expr.formula.Atom
import gapt.logic.Polarity
import gapt.proofs.lk.transformations.folSkolemize

extension (clauseSet: Set[HOLClause])
  /**
    * @return the first-order universal closure of the conjunction of the clauses in the set.
    */
  def toFormula: Formula = {
    val quantifierFreePart = And(clauseSet.map(_.toFormula))
    All.Block(freeFOLVariables(quantifierFreePart).toSeq, quantifierFreePart)
  }

/**
  * @param expr expression to get the free first-order variables of
  * @return the set of first-order variables in [[expr]]
  */
def freeFOLVariables(expr: Expr): Set[FOLVar] =
  (freeVariables(expr) -- freeHOVariables(expr)).map { case v: FOLVar => v }

/**
  * A predicate elimination problem describes a formula of the form ∃X₁ ... ∃Xₙ φ where φ is first-order
  * and we have separated the first-order part from the second-order quantifiers.
  * 
  * This is a common data structure used that describes the input for algorithms solving (witnessed) second-order quantifier elimination and formula equations
  *
  * @param varsToEliminate the variables that are quantified over and are to be eliminated
  * @param firstOrderPart first-order part of the predicate elimination problem that is not allowed to contain second-order quantifiers
  * 
  * Since [[firstOrderPart]] needs to contain the second-order variables of the predicate elimination problem we cannot enforce that formula is a [[gapt.expr.formula.fol.FOLFormula]]
  */
case class PredicateEliminationProblem(
    varsToEliminate: Seq[Var],
    firstOrderPart: Formula
):
  /**
    * @return The formula ∃X₁ ... ∃Xₙ φ where φ is the first-order part of the predicate elimination problem and X₁,...,Xₙ are the variables to eliminate
    */
  def toFormula: Formula = Ex.Block(varsToEliminate, firstOrderPart)

  /**
    * @return The clause set form of the predicate elimination problem by applying skolemization and computing the CNF of the result. 
    * Note that this transformation is not equivalence-preserving as arbitrary new Skolem constants can be introduced.
    */
  def toClauseSet: ClauseSetPredicateEliminationProblem =
    ClauseSetPredicateEliminationProblem(
      varsToEliminate,
      CNFp(folSkolemize(firstOrderPart, Polarity.InAntecedent))
    )

/**
  * A [[PredicateEliminationProblem]] where the first-order part is given by a first-order clause set.
  *
  * @param variablesToEliminate see [[PredicateEliminationProblem.varsToEliminate]]
  * @param firstOrderClauses a set of first-order clauses describing the first-order part of the predicate elimination problem
  */
case class ClauseSetPredicateEliminationProblem(
    varsToEliminate: Seq[Var],
    firstOrderClauses: Set[HOLClause]
):
  /**
    * @return The formula ∃X₁ ... ∃Xₙ φ where φ is the the universal closure of the conjunction of the clauses in this predicate eliination problem and X₁,...,Xₙ are the variables to eliminate
    */
  def toFormula: Formula =
    PredicateEliminationProblem(
      varsToEliminate,
      firstOrderClauses.toFormula
    ).toFormula
