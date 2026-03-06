package gapt.logic.hol

import org.specs2._
import gapt.expr._
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.expr.subst.Substitution
import org.specs2.matcher.Matcher
import org.specs2.matcher.MustMatchers._
import org.specs2.matcher.MatchResult
import gapt.logic.hol.scan.PointedClause
import gapt.proofs.Ant
import gapt.proofs.Suc
import gapt.proofs.Sequent
import gapt.logic.Polarity

class wscanTest extends Specification {
  import gapt.examples.predicateEliminationProblems._

  def is = s2"""
  This is a specification for the wscan implementation

  It should solve
    solve equation without quantified variable ${exampleWithQuantifiedVariableNotOccurring must
      beSolved(equivalentTo = hof"!u A(u)")}
    treat variables as predicate constants when not given ${exampleWithoutQuantifiedVariables must
      beSolved(equivalentTo = hof"!u X(u)")}
    negation of leibniz equality ${negationOfLeibnizEquality.toClauseSet must
      beSolved(equivalentTo = hof"s_0 != s_2")}
    2-part disjunction ${single2PartDisjunction must beSolved(equivalentTo = Top())}
    3-part disjunction ${single3PartDisjunction must beSolved(equivalentTo = Top())}
    two variable example ${exampleWithTwoVariables must beSolved(
      equivalentTo = hof"a!=b"
    )}
    modal correspondence T axiom ${
      modalCorrespondence.negationOfSecondOrderTranslationOfTAxiom must
        beSolved(equivalentTo = hof"-R(a,a)")
    }
    modal correspondence 4 axiom ${
      modalCorrespondence.negationOfSecondOrderTranslationOf4Axiom must
        beSolved(equivalentTo = hof"R(a,b) & R(b,c) & -R(a,c)")
    }
    non-inductive example with two clauses ${
      exampleWithTwoClauses must beSolved(equivalentTo = hof"!u(B(u) -> A(u))")
    }
    non-inductive example with three clauses ${
      exampleWithThreeClauses must beSolved(equivalentTo = hof"!u(C(u) -> A(u)) & !u(B(u) -> A(u))")
    }
    inductive example with tautology deletion ${
      exampleRequiringTautologyDeletion must beSolved(equivalentTo = hof"!u(A(u) -> B(u))")
    }
    inductive example with subsumption ${
      exampleRequiringSubsumption must beSolved(equivalentTo = hof"!u(A(u) -> C(u)) & !u!v(-A(u) | -B(u,v))")
    }
  """

  val defaultDerivationLimit = 20
  val defaultAttemptLimit = 100
  val defaultWitnessLimit = 2
  val defaultOneSidedOnly = true
  def beSolved(
      equivalentTo: Formula,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Int = defaultDerivationLimit,
      attemptLimit: Int = defaultAttemptLimit,
      witnessLimit: Int = defaultWitnessLimit,
      oneSidedOnly: Boolean = defaultOneSidedOnly
  ): Matcher[ClauseSetPredicateEliminationProblem] = {
    (input: ClauseSetPredicateEliminationProblem) =>
      val derivation = scan(
        input,
        allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
        derivationLimit = Some(derivationLimit),
        attemptLimit = Some(attemptLimit)
      ).get
      val firstOrderEquivalent = derivation.conclusion.toFormula
      val witness = wscan(
        input,
        oneSidedOnly = oneSidedOnly,
        allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
        derivationLimit = Some(derivationLimit),
        attemptLimit = Some(attemptLimit),
        witnessLimit = Some(witnessLimit)
      )

      (derivation must beEliminatingDerivation) and
        (witness must beSome[Substitution].like { wit => wit must beWitnessFor(input, firstOrderEquivalent) }) and
        (firstOrderEquivalent must beEquivalentTo(equivalentTo))
  }
}

def beCorrectDerivation: Matcher[scan.Derivation] = { (derivation: scan.Derivation) =>
  val reasons = scan.reasonsThatDerivationIsIncorrect(derivation).toSeq
  (reasons must beEmpty).mapMessage(_ => s"""derivation has errors:
                                            |${reasons.mkString("\n")}
                                            |
                                            |derivation:
                                            |${gapt.examples.predicateEliminationProblems.printer(derivation)}""".stripMargin)
}

def beEliminatingDerivation: Matcher[scan.Derivation] = { (derivation: scan.Derivation) =>
  (derivation must beCorrectDerivation) && (scan.isEliminating(derivation) must beTrue)
}

def beEquivalentTo(right: Formula): Matcher[Formula] = { (left: Formula) =>
  Escargot.isValid(Iff(left, right)).must(beTrue).mapMessage(_ => s"$left is not equivalent to $right")
}

def beSubsetOf(right: Set[Var]): Matcher[Set[Var]] = { (left: Set[Var]) =>
  forall(left)(right must contain(_)).mapMessage(_ => s"$left is not a subset of $right")
}

def beWitnessFor(input: ClauseSetPredicateEliminationProblem, firstOrderEquivalent: Formula): Matcher[Substitution] = {
  (witness: Substitution) =>
    {
      val substitutedInput = BetaReduction.betaNormalize(witness(input.firstOrderClauses.toFormula))
      witness.domain.must(beSubsetOf(input.varsToEliminate.toSet))
        .mapMessage(err => s"domain of substitution is not a subset of variables to eliminate ${input.varsToEliminate}: $err")
        .and(substitutedInput.must(beEquivalentTo(firstOrderEquivalent))
          .mapMessage(_ => s"substituted input is not equivalent to output clause set"))
    }
}

def beEquivalentTo(witness: Substitution) = { (wit: Substitution) =>
  (wscan.areEquivalent(Top(), witness, wit) must beTrue)
    .mapMessage(_ => s"$wit is not equivalent to expected witness $witness")
}

class witnessConstruction extends mutable.Specification {
  import scan._

  "derivation with one-sided purified clause deletion" in {
    val input = ClauseSetPredicateEliminationProblem(
      Seq(hov"X:i>o"),
      Set(hcl":- B(a,v)", hcl":- X(a)", hcl"X(u) :- B(u,v), X(v)", hcl"X(c) :- ")
    )
    val derivation = Derivation(
      input,
      List(
        DerivationStep.ConstraintResolution(
          PointedClause(hcl":- X(a)", Suc(0)),
          PointedClause(hcl"X(c) :-", Ant(0))
        ),
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl":- X(a)", Suc(0))),
        DerivationStep.ExtendendPurityDeletion(hov"X:i>o", Polarity.Negative)
      )
    )
    val wit = wscan.witness(derivation, witnessLimit = None).get
    (derivation must beEliminatingDerivation) and
      (wit must beWitnessFor(input, derivation.conclusion.toFormula)) and
      (wit must beEquivalentTo(Substitution((hov"X:i>o", le"^u u=a"))))
  }

  "derivation with non-one-sided purified clause deletion" in {
    val input = ClauseSetPredicateEliminationProblem(
      Seq(hov"X:i>o"),
      Set(hcl":- B(a,v)", hcl":- X(a)", hcl"X(u) :- B(u,v), X(v)", hcl"X(c) :- ")
    )
    val derivation = Derivation(
      input,
      List(
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl"X(u) :- B(u,v), X(v)", Ant(0))),
        DerivationStep.ConstraintResolution(
          PointedClause(hcl":- X(a)", Suc(0)),
          PointedClause(hcl"X(c) :-", Ant(0))
        ),
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl":- X(a)", Suc(0))),
        DerivationStep.ExtendendPurityDeletion(hov"X:i>o", Polarity.Negative)
      )
    )
    val wit = wscan.witness(derivation, witnessLimit = None).get
    (derivation must beEliminatingDerivation) and
      (wit must beWitnessFor(input, derivation.conclusion.toFormula)) and
      (wit must beEquivalentTo(Substitution((hov"X:i>o", le"^u u=a & !v B(u,v)"))))
  }

  "derivation with cylcic purification subsumption graph and finite witness construction should not yield witness" in {
    val derivation = Derivation(
      ClauseSetPredicateEliminationProblem(
        Seq(hov"X:i>o"),
        Set(hcl"X(v) :- X(f(v))", hcl":- X(f(f(v)))")
      ),
      List(
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl"X(v) :- X(f(v))", Ant(0))),
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl":- X(f(f(v)))", Suc(0)))
      )
    )
    val wit = wscan.witness(derivation, witnessLimit = Some(10))
    (derivation must beEliminatingDerivation) and
      (wit must beNone)
  }

  "non-one-sided derivation with cyclic purification subsumption graph and finite lRes should produce witness" in {
    val input = ClauseSetPredicateEliminationProblem(
      Seq(hov"X:i>i>o"),
      Set(hcl"X(u,v) :- X(v,u)", hcl":- X(a,b)", hcl":- X(b,a)", hcl"X(c,d) :-")
    )
    val derivation = Derivation(
      input,
      List(
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl"X(u,v) :- X(v,u)", Ant(0))),
        DerivationStep.ConstraintResolution(
          PointedClause(hcl"X(c,d) :-", Ant(0)),
          PointedClause(hcl":- X(a,b)", Suc(0))
        ),
        DerivationStep.ConstraintResolution(
          PointedClause(hcl"X(c,d) :-", Ant(0)),
          PointedClause(hcl":- X(b,a)", Suc(0))
        ),
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl"X(c,d) :-", Ant(0))),
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl":- X(a,b)", Suc(0))),
        DerivationStep.PurifiedClauseDeletion(PointedClause(hcl":- X(b,a)", Suc(0)))
      )
    )
    val wit = wscan.witness(derivation, witnessLimit = Some(10)).get
    (derivation must beEliminatingDerivation) and
      (wit must beWitnessFor(input, derivation.conclusion.toFormula)) and
      (wit must beEquivalentTo(Substitution((hov"X:i>i>o", le"^u^v (u != c | v != d) & (u != d | v != c)"))))
  }
}

class scanDerivationsCorrectTest extends mutable.Specification {
  def derivations(
      example: ClauseSetPredicateEliminationProblem,
      derivationLimit: Option[Int],
      derivationCount: Option[Int]
  ): Seq[scan.Derivation] = {
    val derivationIter = scan.derivationsFrom(example, derivationLimit = derivationLimit).map(_.merge)
    val iter = derivationCount match
      case Some(count) => derivationIter.take(count)
      case None        => derivationIter

    iter.toSeq
  }

  "scan derivations must be correct" in {
    import gapt.examples.predicateEliminationProblems.examples

    examples.flatMap(example =>
      // test deep derivations
      derivations(example, derivationLimit = Some(15), derivationCount = Some(5))
      // and shallow ones
        ++ derivations(example, derivationLimit = Some(5), derivationCount = Some(20))
    ) must forall(beCorrectDerivation)
  }
}

class purifiedAndSubsumptionTest extends mutable.Specification {
  import scan.{isLSubsumed, isInjectivelySubsumedAfterVariableElimination, isPurified}

  "X(u) X-subsumes X(a)" in {
    isLSubsumed(hov"X:i>o", Polarity.InSuccedent, hcl":- X(u)", hcl":- X(a)") must beTrue
  }

  "X(u,a) | X(a, u) not X-subsumes X(a,a)" in {
    isLSubsumed(hov"X:i>i>o", Polarity.InSuccedent, hcl":- X(u,a), X(a,u)", hcl":- X(a, a)") must beFalse
  }

  "X(u,a) | X(a, u) Y-subsumes X(a,a)" in {
    isLSubsumed(hov"Y:i>o", Polarity.InSuccedent, hcl":- X(u,a), X(a,u)", hcl":- X(a, a)") must beTrue
  }

  "X(a) not X-subsumes v!=a | X(v)" in {
    isLSubsumed(hov"X:i>o", Polarity.InSuccedent, hcl":- X(a)", hcl"v=a :- X(v)") must beFalse
  }

  "¬X(a,u,b) | ¬X(u,a,b) | X(a,b,c) not ¬X-subsumes -X(a,a,b) | X(a,a,c)" in {
    isLSubsumed(hov"X:i>i>i>o", Polarity.InAntecedent, hcl"X(a,u,b), X(u,a,b) :- X(u,a,c)", hcl"X(a,a,b) :- X(a,a,c)") must beFalse
  }

  "¬X(a,u,b) | ¬X(u,a,b) | X(u,a,c) X-subsumes ¬X(a,a,b) | X(a,a,c)" in {
    isLSubsumed(hov"X:i>i>i>o", Polarity.InSuccedent, hcl"X(a,u,b), X(u,a,b) :- X(a,b,c)", hcl"X(a,a,b) :- X(a,a,c)") must beFalse
  }

  "X(u) X-velim-subsumes X(a)" in {
    isInjectivelySubsumedAfterVariableElimination(hov"X:i>o", Polarity.InSuccedent, hcl":- X(u)", hcl":- X(a)") must beTrue
  }

  "X(u,a) | X(a, u) not X-velim-subsumes X(a,a)" in {
    isInjectivelySubsumedAfterVariableElimination(hov"X:i>i>o", Polarity.InSuccedent, hcl":- X(u,a), X(a,u)", hcl":- X(a, a)") must beFalse
  }

  "X(a) X-velim-subsumes X(a)" in {
    isInjectivelySubsumedAfterVariableElimination(hov"X:i>o", Polarity.InSuccedent, hcl":- X(a)", hcl":- X(a)") must beTrue
  }

  "X(a) X-velim-subsumes v != a | X(v)" in {
    isInjectivelySubsumedAfterVariableElimination(hov"X:i>o", Polarity.InSuccedent, hcl":- X(a)", hcl"v=a :- X(v)") must beTrue
  }

  "X(a) X-velim-subsumes v!=w | w!=a | X(v)" in {
    isInjectivelySubsumedAfterVariableElimination(hov"X:i>o", Polarity.InSuccedent, hcl":- X(a)", hcl"v=w, w=a :- X(v)") must beTrue
  }

  "X(f(u)) not X-velim-subsumes w!=f(v) | X(w)" in {
    isInjectivelySubsumedAfterVariableElimination(hov"X:i>o", Polarity.InSuccedent, hcl":- X(f(u))", hcl"w=f(v) :- X(w)") must beTrue
  }

  "-A(u_0) | X(v_0) X-velim-subsumes v_0 != u_1 | -A(u_0) | X(v_1)" in {
    isInjectivelySubsumedAfterVariableElimination(
      hov"X:i>o",
      Polarity.InSuccedent,
      hcl"A(u_0) :- X(v_0)",
      hcl"v_0 = u_1, A(u_0) :- X(v_1)"
    ) must beTrue
  }

  "[X(a)] is purified in {}" in {
    isPurified(PointedClause(hcl":- X(a)", Suc(0)), Set.empty) must beTrue
  }

  "[X(a)] is not purified in {-X(c)}" in {
    isPurified(PointedClause(hcl":- X(a)", Suc(0)), Set(hcl"X(c) :-")) must beFalse
  }

  "[X(a)] is purified in {-X(c), a!=c}" in {
    isPurified(PointedClause(hcl":- X(a)", Suc(0)), Set(hcl"X(c) :-", hcl"a=c :-")) must beTrue
  }

  "[X(a)] is not purified in {-X(c), c!=a}" in {
    isPurified(PointedClause(hcl":- X(a)", Suc(0)), Set(hcl"X(c) :-", hcl"c=a :-")) must beFalse
  }

  "[-X(u)] | B(u,v) | X(v) is purified in {X(a), B(a,v), -X(c)}" in {
    isPurified(PointedClause(hcl"X(u) :- B(u,v), X(v)", Ant(0)), Set(hcl":- X(a)", hcl":- B(a,v)", hcl"X(c) :-")) must beTrue
  }

  "¬X(u) | B(u,v) | [X(v)] is not purified in {X(a), B(a,v), -X(c)}" in {
    isPurified(PointedClause(hcl"X(u) :- B(u,v), X(v)", Suc(1)), Set(hcl":- X(a)", hcl":- B(a,v)", hcl"X(c) :-")) must beFalse
  }

  "¬X(v) | X(f(v)) | B(v) is not purified in {X(a) | -X(f(a)), X(b), -X(c), B(b)}" in {
    isPurified(
      PointedClause(hcl"X(v) :- X(f(v)), B(v)", Ant(0)),
      Set(hcl"X(f(a)) :- X(a)", hcl":- X(b)", hcl"X(c) :-", hcl":- B(b)")
    ) must beFalse
  }
}
