package gapt.logic.hol

import org.specs2._
import gapt.expr._
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.expr.subst.Substitution
import org.specs2.matcher.Matcher
import org.specs2.matcher.MatchResult
import gapt.logic.hol.wdls.simplify
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.ty.Ty
import gapt.expr.ty.FunctionType
import gapt.expr.given
import org.specs2.specification.core.Fragments
import gapt.logic.hol.scan.nonRedundantResolutionInferences
import gapt.proofs.HOLClause
import gapt.logic.hol.scan.PointedClause
import gapt.proofs.Ant
import gapt.proofs.Suc
import gapt.logic.hol.scan.DerivationStep
import gapt.expr.formula.hol.freeHOVariables
import gapt.proofs.RichFormulaSequent
import gapt.proofs.Sequent
import gapt.logic.hol.scan.constraintResolvent

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

class newWscanTest extends mutable.Specification {
  val showIntermediateValues = false;

  "two different graph topologies" >> {
    val N = Set[HOLClause](
      hcl":- X(a,b)",
      hcl":- X(b,a)",
      hcl":- X(f(b), f(a)), B(b, a)",
      hcl":- B(f(b), f(a))"
    )
    val P = PointedClause(hcl"X(v_1, v_2) :- X(v_2, v_1), X(f(v_1), f(v_2)), B(v_1, v_2)", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)
    val P_1 = P.subPointedClause(Set(Suc(0), Suc(2)))
    val P_2 = P.subPointedClause(Set(Suc(1), Suc(2)))
    val P_3 = P.subPointedClause(Set(Suc(2)))
    "witness for two cycle graph" >> testWitness(P, N, resolutionStepWitness(Seq(P_1)))
    "witness for acyclic graph" >> testWitness(P, N, resolutionStepWitness(Seq(P, P_2, P_3)))
  }

  "two connected components" >> {
    val N = Set[HOLClause](
      hcl":- X(a,b)",
      hcl":- X(b,a), X(f(a), f(b))",
      hcl":- X(b,a), X(f(b), f(a))",
      hcl":- X(c,d)",
      hcl":- X(g(c), g(d))",
      hcl":- X(g(d), g(c))",
      hcl":- X(f(g(d)), f(g(c)))",
      hcl":- X(f(g(c)), f(g(d)))"
    )
    val P = PointedClause(hcl"X(v_1, v_2) :- X(v_2, v_1), X(f(v_1), f(v_2)), X(g(v_1), g(v_2))", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)
    val P_1 = P.subPointedClause(Set(Suc(0)))
    val P_2 = P.subPointedClause(Set(Suc(1)))
    val P_3 = P.subPointedClause(Set(Suc(2)))

    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P, P_1)))
  }

  "cycle occurring at different stages" >> {
    val N = Set[HOLClause](
      hcl":- X(a,b)",
      hcl":- X(f(a), f(b))",
      hcl":- X(f(b), f(a))",
      hcl":- X(c,d)",
      hcl":- X(f(c), f(d))",
      hcl":- X(f(f(c)), f(f(d)))",
      hcl":- X(f(f(d)), f(f(c)))"
    )
    val P = PointedClause(hcl"X(v_1, v_2) :- X(v_2, v_1), X(f(v_1), f(v_2))", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)
    val P_1 = P.subPointedClause(Set(Suc(0)))
    val P_2 = P.subPointedClause(Set(Suc(1)))
    val P_3 = P.subPointedClause(Set(Suc(0), Suc(1)))
    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P, P, P_1)))
  }

  "cycle of length 3" >> {
    val N = Set[HOLClause](
      hcl":- X(a,b,c)",
      hcl":- X(f(a), f(b), f(c))",
      hcl":- X(f(b), f(c), f(a))",
      hcl":- X(f(c), f(a), f(b))",
      hcl":- X(a_1,b_1,c_1)",
      hcl":- X(f(a_1), f(b_1), f(c_1))",
      hcl":- X(f(f(a_1)), f(f(b_1)), f(f(c_1)))",
      hcl":- X(f(f(b_1)), f(f(c_1)), f(f(a_1)))",
      hcl":- X(f(f(c_1)), f(f(a_1)), f(f(b_1)))"
    )
    val P = PointedClause(hcl"X(v_1, v_2, v_3) :- X(v_2, v_3, v_1), X(f(v_1), f(v_2), f(v_3)), X(g(v_1), g(v_2), g(v_3))", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)

    val P_1 = P.subPointedClause(Set(Suc(0)))
    val P_2 = P.subPointedClause(Set(Suc(1)))
    val P_3 = P.subPointedClause(Set(Suc(0), Suc(1)))

    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P_3, P_3, P_1, P_1)))
  }

  "multiple literals" >> {
    val N = Set[HOLClause](
      hcl":- X(a)",
      hcl":- X(f(a)), X(g(a))",
      hcl":- X(f(f(a))), X(g(f(a))), X(g(a))",
      hcl":- B(f(f(a)))",
      hcl":- B(g(f(a)))",
      hcl":- B(g(a))"
    )
    val P = PointedClause(hcl"X(v) :- X(f(v)), X(g(v)), B(v)", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)

    val P_1 = P.subPointedClause(Set(Suc(0), Suc(1)))
    val P_2 = P.subPointedClause(Set(Suc(2)))
    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P, P, P_2)))
  }

  "cycle with different steps" >> {
    val N = Set[HOLClause](
      hcl":- X(a,b,c)",
      hcl":- X(b,c,a)"
    )
    val P = PointedClause(hcl"X(u,v,w) :- X(v,w,u), X(w,u,v)", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)

    val P_1 = P.subPointedClause(Set(Suc(0)))
    val P_2 = P.subPointedClause(Set(Suc(1)))
    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P)))
  }

  "incoming and outgoing from cycle" >> {
    val N = Set[HOLClause](
      hcl":- X(a, b)",
      hcl":- X(f(a), f(b))",
      hcl":- X(f(b), f(a)), X(f(f(a)), f(f(b)))",
      hcl":- B(f(f(a)), f(f(b)))"
    )
    val P = PointedClause(hcl"X(u,v) :- X(v,u), X(f(u), f(v)), B(u,v)", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)

    val P_1 = P.subPointedClause(Set(Suc(0)))
    val P_2 = P.subPointedClause(Set(Suc(1)))
    val P_3 = P.subPointedClause(Set(Suc(2)))
    val P_4 = P.subPointedClause(Set(Suc(0), Suc(2)))
    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P, P, P_4)))
  }

  "different cycle lengths between N and P" >> {
    val N = Set[HOLClause](
      hcl":- X(a, a, a)"
    )
    val P = PointedClause(hcl"X(u,v,w) :- X(v,w,u)", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)

    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P, P)))
  }

  "different cycle lengths in different components" >> {
    val N = Set[HOLClause](
      hcl":- X(a_1, a_2, a_3)",
      hcl":- X(a_2, a_1, a_3)",
      hcl":- X(a_2, a_3, a_1)",
      hcl":- X(b, c, d)",
      hcl":- X(c, b, d)"
    )
    val P = PointedClause(hcl"X(u,v,w) :- X(v,u,w), X(u,w,v), X(v,w,u)", Ant(0))
    val P_1 = P.subPointedClause(Set(Suc(0)))
    val P_2 = P.subPointedClause(Set(Suc(1)))
    val P_3 = P.subPointedClause(Set(Suc(2)))
    testPurifiedClauseDeletionAssumptions(P, N)

    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P, P)))
  }

  "example where clause set required to subsume witness substitution in P" >> {
    val N = Set[HOLClause](
      hcl":- X(f(f(w)))"
    )
    val P = PointedClause(hcl"X(v) :- X(f(v))", Ant(0))
    testPurifiedClauseDeletionAssumptions(P, N)

    "witness" >> testWitness(P, N, resolutionStepWitness(Seq(P)))
  }

  def testPurifiedClauseDeletionAssumptions(pointedClause: PointedClause, clauseSet: Set[HOLClause]): Fragments = {
    "purified clause deletion assumptions" >> {
      val missingResolutions = nonRedundantResolutionInferences(clauseSet, pointedClause)
      if missingResolutions.isEmpty then {
        "no missing resolvents" in success
      } else {
        "missing resolvents" >> {
          Fragments.foreach(missingResolutions) {
            case DerivationStep.ConstraintResolution(left, right) =>
              assert(left == pointedClause, s"left was not the pointed clause")
              step(ko(s"resolvent ${{ constraintResolvent(left, right)._1 }} from resolution between $left and $right is not redundant"))
          }
        }
      }

      def isRedundancyEliminated(clauses: Set[HOLClause]): Boolean = {
        scan.redundancyStep(scan.State(
          clauses,
          scan.Derivation.emptyFrom(
            ClauseSetPredicateEliminationProblem(Seq(hov"X"), clauses)
          ),
          remainingAllowedInferences = None,
          oneSidedOnly = false,
          allowResolutionOnBaseLiterals = true
        )).isEmpty
      }

      if isRedundancyEliminated(clauseSet + pointedClause.clause) then {
        "N + P is redundancy eliminated" >> success
      } else {
        step(ko(s"N + P is not redundancy eliminated"))
      }

      // TODO: check that all clauses are in avelim-NF

    }
  }

  def testWitness(pointedClause: PointedClause, clauseSet: Set[HOLClause], witness: Substitution): Fragments = {
    val P = pointedClause.clause.toFormula.foUniversalClosure
    val N = clauseSet.toFormula.foUniversalClosure

    if Escargot.isValid(N --> N.applySubstitution(witness).betaNormalized) then {
      "N -> N[X<-wit] is valid" in success
    } else {
      "N -> N[X<-wit] is not valid" in failure
    }

    if Escargot.isValid(N --> P.applySubstitution(witness).betaNormalized) then {
      "N -> P[X<-wit] is valid" in success
    } else {
      "N -> P[X<-wit] is not valid" in failure
    }
  }

  extension (f: Formula) {
    def foUniversalClosure: Formula = All.Block(freeFOLVariables(f).toSeq, f)
  }

  extension (e: Expr) {
    def simplified: Expr = {
      e.betaNormalized match {
        case Abs.Block(vars, f: Formula) => Abs.Block(vars, simplify(f))
      }
    }
  }

  def alphaStep(P: PointedClause, placeholder: Var): Expr = {
    assert(P.varOption.isDefined)
    val freeFolVars = freeFOLVariables(P.clause.toFormula).toSeq
    val args = rename.awayFrom(freeFolVars).freshStream("u").zip(P.args).map {
      case (name, arg) => Var(name, arg.ty)
    }
    val (designatedLiteral, reproductionArgs, remainder) = P.decomposed
    val reproductions = Sequent(Vector.empty[Atom], reproductionArgs.elements.map(args => Atom(placeholder, args)))
    val constraint = HOLClause(args.zip(P.args).map((a, b) => Eq(a, b)), Vector.empty[Atom])
    val firstClause = App(P.varOption.get, args).betaNormalized
    val formula: Formula = And(
      if P.index.isAnt then firstClause else Neg(firstClause),
      All.Block(freeFolVars, (constraint ++ remainder ++ reproductions).toFormula)
    ).betaNormalized
    Abs.Block(args, formula).simplified
  }

  def alpha(P: PointedClause, k: Int, initial: Expr): Expr = {
    val placeholder = rename.awayFrom(freeVariables(P.clause.toFormula)).fresh(Var("W", P.symbol.ty))
    if k == 0 then initial
    else {
      val previous = alpha(P, k - 1, initial)
      alphaStep(P, placeholder).substitute((placeholder, previous)).simplified
    }
  }

  def beta(P: PointedClause, k: Int): Expr = {
    alpha(P, k, P.varOption.get).simplified
  }

  def delta(P: PointedClause, k: Int): Expr = {
    def freshArgumentVariables(ty: Ty, varName: String, blacklist: Iterable[VarOrConst] = Iterable.empty) = {
      val FunctionType(_, argTypes) = ty: @unchecked
      rename.awayFrom(blacklist).freshStream(varName).zip(argTypes).map(Var(_, _))
    }

    val freshVars = freshArgumentVariables(P.symbol.ty, "u", freeVariables(P.clause.toFormula))
    val bot = Abs.Block(freshVars, Bottom())
    alpha(P, k, bot).simplified
  }

  def neg(p: Expr): Expr = p match {
    case Abs.Block(vars, inner) => Abs.Block(vars, Neg(inner))
  }

  def resolutionStepWitness(Ps: Seq[PointedClause]): Substitution = {
    Ps.foldRight(Substitution()) { (next, acc) =>
      val nextVar = next.varOption.get
      val renamedVar = rename.awayFrom(freeHOVariables(next.clause.toFormula)).fresh(nextVar)
      val expr = alphaStep(next, renamedVar).substitute((renamedVar, acc(nextVar)))
      Substitution((nextVar, expr.simplified))
    }
  }
}
