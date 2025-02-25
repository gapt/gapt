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
    solve equation without quantified variable ${exampleWithQuantifiedVariableNotOccurring must beSolved()}
    treat variables as predicate constants when not given ${exampleWithoutQuantifiedVariables must beSolved()}
    negation of leibniz equality ${negationOfLeibnizEquality.toClauseSet must beSolved()}
    resolution on base literals ${exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables must beSolved(allowResolutionOnBaseLiterals = true)}
    2-part disjunction ${single2PartDisjunction must beSolved()}
    3-part disjunction ${single3PartDisjunction must beSolved()}
    two variable example ${exampleWithTwoVariables must beSolved()}
    modal correspondence T axiom ${modalCorrespondence.negationOfSecondOrderTranslationOfTAxiom must beSolved()}
    modal correspondence 4 axiom ${modalCorrespondence.negationOfSecondOrderTranslationOf4Axiom must beSolved()}
    non-inductive example with two clauses ${exampleWithTwoClauses must beSolved()}
    non-inductive example with three clauses ${exampleWithThreeClauses must beSolved()}
    inductive example with tautology deletion ${exampleRequiringTautologyDeletion must beSolved()}
    inductive example with subsumption ${exampleRequiringSubsumption must beSolved()}
  """

  def beEquivalentTo(right: Formula): Matcher[Formula] = { (left: Formula) =>
    Escargot.isValid(Iff(left, right)).must(beTrue).mapMessage(_ => s"$left is not equivalent to $right")
  }

  def beCorrectSolutionFor(input: ClauseSetPredicateEliminationProblem, firstOrderEquivalent: Formula): Matcher[Option[Substitution]] = {

    (solution: Option[Substitution]) =>
      solution must beSome[Substitution].like {
        (witness: Substitution) =>
          {
            val substitutedInput = BetaReduction.betaNormalize(witness(input.firstOrderClauses.toFormula))
            witness.domain.mustEqual(input.varsToEliminate.toSet)
              .mapMessage(_ => s"domain of substitution is not ${input.varsToEliminate}")
              .and(substitutedInput.must(beEquivalentTo(firstOrderEquivalent))
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
      val firstOrderEquivalent = scan(
        input,
        allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
        derivationLimit = Some(derivationLimit),
        attemptLimit = Some(attemptLimit)
      ).get.conclusion.toFormula
      wscan(
        input,
        oneSidedOnly = true,
        allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
        derivationLimit = Some(derivationLimit),
        attemptLimit = Some(attemptLimit),
        witnessLimit = Some(witnessLimit)
      ).must(beCorrectSolutionFor(input, firstOrderEquivalent))
  }
}
