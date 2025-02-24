package gapt.logic.hol.scan

import org.specs2._
import gapt.proofs._
import gapt.expr._
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.logic.hol.scan.scan.freeFOLVariables
import gapt.expr.subst.Substitution
import gapt.logic.hol.scan.scan.Derivation
import gapt.logic.hol.ClauseSetPredicateEliminationProblem
import org.specs2.matcher.Matcher
import org.specs2.Specification
import gapt.proofs.resolution.structuralCNF
import gapt.logic.hol.scan.scan.PointedClause
import gapt.logic.hol.scan.scan.Inference
import gapt.expr.formula.hol.freeHOVariables
import org.specs2.matcher.MatchResult

class ScanTest extends Specification {
  import gapt.examples.predicateEliminationProblems._

  def is = s2"""
  This is a specification for the scan implementation

  It should solve
    solve equation without quantified variable ${exampleWithQuantifiedVariableNotOccurring.toClauseSet must beSolved()}
    treat variables as predicate constants when not given ${exampleWithoutQuantifiedVariables.toClauseSet must beSolved()}
    negation of leibniz equality ${negationOfLeibnizEquality.toClauseSet must beSolved()}
    resolution on non-base literals ${exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables.toClauseSet must beSolved()}
    2-part disjunction ${single2PartDisjunction.toClauseSet must beSolved()}
    3-part disjunction ${single3PartDisjunction.toClauseSet must beSolved()}
    two variable example ${exampleWithTwoVariables.toClauseSet must beSolved()}
    modal correspondence T axiom ${modalCorrespondence.negationOfSecondOrderTranslationOfTAxiom.toClauseSet must beSolved()}
    modal correspondence 4 axiom ${modalCorrespondence.negationOfSecondOrderTranslationOf4Axiom.toClauseSet must beSolved()}
    non-inductive example with two clauses ${exampleWithTwoClauses.toClauseSet must beSolved()}
    non-inductive example with three clauses ${exampleWithThreeClauses.toClauseSet must beSolved()}
    inductive example with tautology deletion ${exampleRequiringTautologyDeletion.toClauseSet must beSolved()}
    inductive example with subsumption ${exampleRequiringSubsumption.toClauseSet must beSolved()}
    unsatisfiable example which requires factoring ${unsatisfiableExampleThatRequiresFactoring.toClauseSet must beSolved()}
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

  def beCorrectSolutionFor(input: ClauseSetPredicateEliminationProblem): Matcher[Either[Derivation, (Set[HOLClause], Option[Substitution], Derivation)]] = { (result: Either[Derivation, (Set[HOLClause], Option[Substitution], Derivation)]) =>
    result must beRight.like {
      case output @ (clauseSet: Set[HOLClause], Some(witnesses: Substitution), derivation: Derivation) =>
        val substitutedInput = witnesses(input.clauses).map(_.toFormula).map(BetaReduction.betaNormalize)
        val beWithoutQuantifiedVariables: Matcher[HOLClause] = { (c: HOLClause) =>
          {
            (freeHOVariables(c.toFormula).intersect(input.variablesToEliminate).isEmpty, s"$c contains at least one quantified variable from ${input.variablesToEliminate}")
          }
        }

        clauseSet.must(contain(beWithoutQuantifiedVariables).foreach)
          .and(witnesses.domain.mustEqual(input.variablesToEliminate)
            .mapMessage(_ => s"domain of substitution is not ${input.variablesToEliminate}"))
          .and(substitutedInput.must(beEquivalentTo(clauseSet.map(_.toFormula)))
            .mapMessage(_ => s"substituted input is not equivalent to output clause set"))
    }
  }

  val defaultDerivationLimit = 100
  val defaultPossibilityLimit = 10
  def beSolved(derivationLimit: Int = defaultDerivationLimit, possibilityLimit: Int = defaultPossibilityLimit): Matcher[ClauseSetPredicateEliminationProblem] = {
    (input: ClauseSetPredicateEliminationProblem) =>
      scan(input, Some(derivationLimit)).take(possibilityLimit).toSeq.must(contain(beCorrectSolutionFor(input)))
  }
}
