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
import gapt.logic.hol.scan.scan.ResolutionCandidate
import gapt.logic.hol.scan.scan.Inference
import gapt.expr.formula.hol.freeHOVariables
import org.specs2.matcher.MatchResult

class ScanTest extends Specification {
  import gapt.examples.formulaEquations._

  def is = s2"""
  This is a specification for the scan implementation

  It should solve
    solve equation without quantified variable ${quantifiedVariableNotOccurring must beSolved()}
    treat variables as predicate constants when not given ${variablesAsConstants must beSolved()}
    negation of leibniz equality ${negationOfLeibnizEquality must beSolved()}
    resolution on non-base literals ${resolutionOnNonBaseLiterals must beSolved()}
    simple disjunction ${simpleDisjunction must beSolved()}
    triple disjunction ${tripleDisjunction must beSolved()}
    two variable example ${twoVariableExample must beSolved()}
    modal correspondence axiom reflexivity ${modalCorrespondenceReflexivity must beSolved()}
    modal correspondence axiom transitivity ${modalCorrespondenceTransitivity must beSolved()}
    non-inductive example with two clauses ${example must beSolved()}
    non-inductive example with three clauses ${example must beSolved()}
    inductive example with tautology deletion ${exampleRequiringTautologyDeletion must beSolved()}
    inductive example with subsumption ${exampleRequiringSubsumption must beSolved()}
  """

  def beEquivalentTo(right: Formula): Matcher[Formula] = { (left: Formula) =>
    Escargot.isValid(Iff(left, right)).must(beTrue).mapMessage(_ => s"$left is not equivalent to $right")
  }

  def beEquivalentTo(right: Set[Formula]): Matcher[Set[Formula]] = { (left: Set[Formula]) =>
    val leftFree = And(left)
    val rightFree = And(right)
    val leftFormula = All.Block(freeFOLVariables(leftFree).toSeq, leftFree)
    val rightFormula = All.Block(freeFOLVariables(rightFree).toSeq, rightFree)
    (leftFormula must beEquivalentTo(rightFormula)).mapMessage(_ => s"$left is not equivalent to $right")
  }

  def beCorrectSolutionFor(input: FormulaEquationClauseSet): Matcher[Either[Derivation, (Set[HOLClause], Option[Substitution], Derivation)]] = { (result: Either[Derivation, (Set[HOLClause], Option[Substitution], Derivation)]) =>
    result must beRight.like {
      case output @ (clauseSet: Set[HOLClause], Some(witnesses: Substitution), derivation: Derivation) =>
        val substitutedInput = witnesses(input.clauses).map(_.toFormula).map(BetaReduction.betaNormalize)
        val beWithoutQuantifiedVariables: Matcher[HOLClause] = { (c: HOLClause) =>
          {
            (freeHOVariables(c.toFormula).intersect(input.quantifiedVariables).isEmpty, s"$c contains at least one quantified variable from ${input.quantifiedVariables}")
          }
        }

        clauseSet.must(contain(beWithoutQuantifiedVariables).foreach)
          .and(witnesses.domain.mustEqual(input.quantifiedVariables)
            .mapMessage(_ => s"domain of substitution is not ${input.quantifiedVariables}"))
          .and(substitutedInput.must(beEquivalentTo(clauseSet.map(_.toFormula)))
            .mapMessage(_ => s"substituted input is not equivalent to output clause set"))
    }
  }

  val defaultLimit = 100
  def beSolved(limit: Int = defaultLimit): Matcher[FormulaEquationClauseSet] = {
    (input: FormulaEquationClauseSet) =>
      scan(input, Some(limit)).toSeq.must(contain(beCorrectSolutionFor(input)).foreach)
  }
}
