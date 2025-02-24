package gapt.logic.hol

import org.specs2._
import gapt.proofs._
import gapt.expr._
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.logic.hol.scan.freeFOLVariables
import gapt.expr.subst.Substitution
import gapt.logic.hol.scan.Derivation
import gapt.logic.hol.ClauseSetPredicateEliminationProblem
import org.specs2.matcher.Matcher
import org.specs2.Specification
import gapt.proofs.resolution.structuralCNF
import gapt.logic.hol.scan.PointedClause
import gapt.logic.hol.scan.DerivationStep
import gapt.expr.formula.hol.freeHOVariables
import org.specs2.matcher.MatchResult

class wscanTest extends Specification {
  import gapt.examples.predicateEliminationProblems._

  def is = s2"""
  This is a specification for the scan implementation

  It should solve
    solve equation without quantified variable ${exampleWithQuantifiedVariableNotOccurring.toClauseSet must beSolved()}
    treat variables as predicate constants when not given ${exampleWithoutQuantifiedVariables.toClauseSet must beSolved()}
    negation of leibniz equality ${negationOfLeibnizEquality.toClauseSet must beSolved()}
    resolution on base literals ${exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables.toClauseSet must beSolved(allowResolutionOnBaseLiterals = true)}
    2-part disjunction ${single2PartDisjunction.toClauseSet must beSolved()}
    3-part disjunction ${single3PartDisjunction.toClauseSet must beSolved()}
    two variable example ${exampleWithTwoVariables.toClauseSet must beSolved()}
    modal correspondence T axiom ${modalCorrespondence.negationOfSecondOrderTranslationOfTAxiom.toClauseSet must beSolved()}
    modal correspondence 4 axiom ${modalCorrespondence.negationOfSecondOrderTranslationOf4Axiom.toClauseSet must beSolved()}
    non-inductive example with two clauses ${exampleWithTwoClauses.toClauseSet must beSolved()}
    non-inductive example with three clauses ${exampleWithThreeClauses.toClauseSet must beSolved()}
    inductive example with tautology deletion ${exampleRequiringTautologyDeletion.toClauseSet must beSolved()}
    inductive example with subsumption ${exampleRequiringSubsumption.toClauseSet must beSolved()}
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

  def beCorrectSolutionFor(input: ClauseSetPredicateEliminationProblem): Matcher[Option[(Derivation, Substitution)]] = {
    (solution: Option[(Derivation, Substitution)]) =>
      solution must beSome[(Derivation, Substitution)].like {
        case (derivation: Derivation, witnesses: Substitution) => {
          val substitutedInput = witnesses(input.firstOrderClauses).map(_.toFormula).map(BetaReduction.betaNormalize)
          val beWithoutQuantifiedVariables: Matcher[HOLClause] = {
            (c: HOLClause) =>
              {
                (freeHOVariables(c.toFormula).intersect(input.varsToEliminate.toSet).isEmpty, s"$c contains at least one quantified variable from ${input.varsToEliminate}")
              }
          }

          val clauseSet = derivation.conclusion
          clauseSet
            .must(contain(beWithoutQuantifiedVariables).foreach)
            .and(witnesses.domain.mustEqual(input.varsToEliminate.toSet)
              .mapMessage(_ => s"domain of substitution is not ${input.varsToEliminate}"))
            .and(substitutedInput.must(beEquivalentTo(clauseSet.map(_.toFormula)))
              .mapMessage(_ => s"substituted input is not equivalent to output clause set"))
        }
      }
  }

  val defaultDerivationLimit = 20
  val defaultAttemptLimit = 100
  val defaultWitnessLimit = 2
  def beSolved(
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Int = defaultDerivationLimit,
      attemptLimit: Int = defaultAttemptLimit,
      witnessLimit: Int = defaultWitnessLimit
  ): Matcher[ClauseSetPredicateEliminationProblem] = {
    (input: ClauseSetPredicateEliminationProblem) =>
      wscan(
        input,
        oneSidedOnly = true,
        allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
        derivationLimit = Some(derivationLimit),
        attemptLimit = Some(attemptLimit),
        witnessLimit = Some(witnessLimit)
      ).must(beCorrectSolutionFor(input))
  }
}
