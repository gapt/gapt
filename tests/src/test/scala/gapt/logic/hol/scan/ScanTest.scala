package gapt.logic.hol.scan

import org.specs2._
import gapt.proofs._
import gapt.expr._
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.logic.hol.scan.scan.freeFOLVariables
import gapt.expr.subst.Substitution
import gapt.logic.hol.scan.scan.Derivation
import org.specs2.matcher.Matcher
import gapt.logic.hol.scan.scan.FormulaEquationClauseSet
import org.specs2.Specification
import gapt.proofs.resolution.structuralCNF
import gapt.examples.Pi2Pigeonhole.proof
import gapt.logic.hol.scan.scan.InferenceStep
import gapt.logic.hol.scan.scan.ResolutionCandidate
import gapt.logic.hol.scan.scan.Inference

class ScanTest extends Specification {
  import gapt.examples.formulaEquations._

  def is = s2"""
  This is a specification for the scan implementation

  It should solve
    negation of leibniz equality ${negationOfLeibnizEquality must beSolved()}
    resolution on non-base literals ${resolutionOnNonBaseLiterals must beSolved()}
    simple disjunction ${simpleDisjunction must beSolved()}
    triple disjunction ${tripleDisjunction must beSolved()}
    two variable example ${twoVariableExample must beSolved()}
  """

  def beEquivalentTo(right: Formula): Matcher[Formula] = { (left: Formula) =>
    Escargot.isValid(Iff(left, right)) must beTrue
  }

  def beEquivalentTo(right: Set[Formula]): Matcher[Set[Formula]] = { (left: Set[Formula]) =>
    val leftFree = And(left)
    val rightFree = And(right)
    val leftFormula = All.Block(freeFOLVariables(leftFree).toSeq, leftFree)
    val rightFormula = All.Block(freeFOLVariables(rightFree).toSeq, rightFree)
    leftFormula must beEquivalentTo(rightFormula)
  }

  val defaultLimit = 100
  def beSolved(limit: Int = defaultLimit): Matcher[FormulaEquationClauseSet] = {
    (input: FormulaEquationClauseSet) =>
      scan(input, Some(limit)) must beRight.like {
        (clauseSet: Set[HOLClause], witnesses: Substitution, derivation: Derivation) =>
          val substitutedInput = witnesses(input.clauses).map(_.toFormula).map(BetaReduction.betaNormalize)
          substitutedInput must beEquivalentTo(clauseSet.map(_.toFormula))
      }
  }
}
