package gapt.examples.predicateEliminationProblems

import gapt.expr._
import gapt.proofs._
import gapt.expr.ty._
import gapt.expr.formula._
import gapt.logic.hol.ClauseSetPredicateEliminationProblem
import gapt.logic.hol.toFormula
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLVar
import gapt.logic.Polarity
import gapt.expr.formula.constants.BottomC

val exampleWithQuantifiedVariableNotOccurring = clspep"?(X:i>o) !u A(u)"
val exampleWithoutQuantifiedVariables = clspep"!u X(u)"
val exampleThatCanBeSolvedByPolarityRuleImmediately = clspep"?X(${
    Set(hcl"A(u) :- X(u)", hcl"B(u,v), X(u) :- X(v)").toFormula
  })"
val negationOfLeibnizEquality = pep"?X?u?v -(X(u) <-> X(v))"

val exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables = clspep"?X(${
    Set(
      hcl":- B(u,v)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"A(u) :- X(u)",
      hcl"X(u) :- C(u)"
    ).toFormula
  })"

val exampleWithTwoClauses = clspep"?X(${
    Set(
      hcl"B(v) :- X(v)",
      hcl"X(u) :- A(u)"
    ).toFormula
  })"

val exampleWithThreeClauses = clspep"?X(${
    Set(hcl"B(v) :- X(v)", hcl"X(u) :- A(u)", hcl"C(u) :- X(u)").toFormula
  })"

val single2PartDisjunction = clspep"?X(X(a) | X(b))"
val single3PartDisjunction = clspep"?X(X(a) | X(b) | X(c))"

val exampleWithTwoVariables = clspep"?X?Y(${
    Set(
      hcl":- Y(a)",
      hcl"Y(u) :- X(u)",
      hcl"X(b) :-"
    ).toFormula
  })"

val exampleRequiringTautologyDeletion = clspep"?X(${
    Set(hcl"A(u) :- X(u)", hcl"X(u) :- X(v), A(u)", hcl"X(u) :- B(u)").toFormula
  })"

val exampleRequiringSubsumption = clspep"?X(${
    Set(
      hcl"A(u), B(u,v) :-",
      hcl"A(u) :- X(u)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(u) :- C(u)"
    ).toFormula
  })"

val exampleWithSymmetryRequiringSubsumption = clspep"?Y(${
    Set(
      hcl"A(u,v), B(u,v) :-",
      hcl"A(u,v) :- Y(u,v)",
      hcl"B(u,v), Y(u,v) :- Y(v,u)",
      hcl"Y(u,v) :- C(u,v)"
    ).toFormula
  })"

val unsatisfiableExampleThatRequiresFactoring = clspep"?(X:i>o)(${
    Set(
      hcl":- X(u), X(f(u))",
      hcl"X(u) :- X(f(v))",
      hcl"X(u), X(f(u)) :-"
    ).toFormula
  })"

val witnessBlowup = clspep"?X(${
    Set(
      hcl"X(c) :- ",
      hcl":- X(a_1), X(b_1)",
      hcl":- X(a_2), X(b_2)"
    ).toFormula
  })"

val twoStepRedundancy = clspep"?X(${
    Set(
      hcl"B(a, v), B(v, w) :-",
      hcl":- X(a)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(c) :-"
    ).toFormula
  })"

val subsumptionByXLiteral = clspep"?X(${
    Set(
      hcl":- X(a,a)",
      hcl"X(u,v) :- X(v,u), B(u,v)",
      hcl"X(b,b) :- X(c,c)",
      hcl"X(d,d) :-"
    ).toFormula
  })"

val badExample = clspep"?X(${
    Set(
      hcl":- B(b,v)",
      hcl":- B(c,v)",
      hcl"X(a) :-",
      hcl":- X(b), X(c)",
      hcl"X(u) :- B(u,v), X(v)"
    ).toFormula
  })"

val booleanUnification = pep"?X?Y((!x (#c(Pat:i>o)(x) & ?y (#c(f:i>i>o)(x,y) & X(y) & ?z (#c(s:i>i>o)(x,z) & #c(Severe:i>o)(z))))) <-> (!x (#c(Pat:i>o)(x) & ?y (#c(f:i>i>o)(x,y) & Y(y) & #c(Inj:i>o)(y) & ?z ((#c(f:i>i>o)(x,z) & #c(Head:i>o)(z)))))))"

val onlyOneSidedClauses = clspep"?X(${
    Set(
      hcl":- X(u), X(v), R(u,v)",
      hcl"X(u), X(v) :- Q(u,v)"
    ).toFormula
  })"

val wernhardExample06Implicative = pep"?X_1?X_2((!u (A(u) -> B(u))) -> (!u(X_1(u) -> X_2(u)) & !u(A(u) -> X_2(u)) & !u(X_2(u) -> B(u))))".toClauseSet
val wernhardExample06Conjunctive = clspep"?X_1?X_2(!u(A(u) -> B(u)) & !u(X_1(u) -> X_2(u)) & !u(A(u) -> X_2(u)) & !u(X_2(u) -> B(u)))"
val wernhardExample06WithoutFirstOrderAssumption = clspep"?X_1?X_2(!u(X_1(u) -> X_2(u)) & !u(A(u) -> X_2(u)) & !u(X_2(u) -> B(u)))"

val soqeBookExample5_4 = pep"?P!x!y?z((-P(a) | Q(x)) & (P(y) | Q(a)) & P(z))".toClauseSet
val soqeBookExample5_7 = clspep"?P?Q(!x(-P(x) | P(f(x)) | Q(x)) & P(a) & Q(b) & -P(b))"
val soqeBookExample6_2_16 = clspep"?X(!x(X(x) -> !y R(x,y)) & (X(a) | X(b)))"
val soqeBookExample6_2_17 = clspep"?X(!x!y(R(x,y) -> X(x)) & (-X(a) | -X(b)))"
val soqeBookExample6_3 = clspep"?X(!x!y(X(x,y) -> R(x,y)) & (X(a,b) | X(b,c)))"
val soqeBookExample6_4 = clspep"?X(!x!y(R(x,y) -> X(x)) & (X(a) | -X(b)) & -X(c))"
val soqeBookExample6_5 = pep"?X(!x?y X(x,y) & !x?y -X(x,y))".toClauseSet
val soqeBookExample6_6 = clspep"?X(!x!y(R(x,y) | X(x) | -X(y)) & !x!y(S(x,y) | X(x) | X(y)))"
val soqeBookExample6_23 = clspep"?X(!x!y(X(y) -> (X(x) | R(x,y))) & !x!y(X(x) | X(y) | S(x,y)))"

val gabbayOhlbachIntroductionExample_1 = clspep"?P((P | Q) & (-P | R))"
val gabbayOhlbachIntroductionExample_2 = clspep"?P((P | Q) & (-P | R) & (-P | S))"
val gabbayOhlbachIntroductionExample_3 = clspep"?P((P(a) | Q) & (-P(b) | R))"
val gabbayOhlbachSymmetryExample = clspep"?P!x!y((P(x,y) -> P(y,x)) & (P(x,y) <-> Q(x,y)))"
val gabbayOhlbachSection3Example = clspep"?P!x!y((P(x,a) | P(a,x) | C(x)) & (-P(y,a) | -P(a,y) | D(y)))"

val eberhardHetzlWellerExample_4 = clspep"?X((X(a) & -X(f(b))) | (X(f(b)) & -X(a)))"

val kloibhoferHetzlExample_42 = clspep"?X?Y(X(a) & !u!v((X(u) & X(v)) -> Y(f(u,v))) & !w(Y(w) -> ${BottomC()}))"

val bachmairGanzingerExample = pep"?P?Q?u!x!y((-P(x) | R(x,x)) & (Q(u,x) | -R(x,u)) & (P(x) | P(y) | -Q(x,y)))".toClauseSet

object modalCorrespondence {
  val negationOfModalAxiom = pep"?X -(!u (!v (R(u,v) -> ((!w (R(v, w) -> X(w))) <-> X(v)))))"
  val negationOfSecondOrderTranslationOfTAxiom = clspep"?X(${
      Set(
        hcl"R(a,v) :- X(v)",
        hcl"X(a) :-"
      ).toFormula
    })"
  val negationOfSecondOrderTranslationOf4Axiom = clspep"?X(${
      Set(
        hcl"R(a,v) :- X(v)",
        hcl":- R(a,b)",
        hcl":- R(b,c)",
        hcl"X(c) :-"
      ).toFormula
    })"
}

object graphReachability {
  def const(node: Int): FOLConst = FOLConst(s"a_$node")
  def edge(from: Int, to: Int): Atom = foa"E(${const(from)}, ${const(to)})"
  def existsPath(from: Int, to: Int, length: Int): FOLFormula = {
    require(length >= 0)
    def pathFrom(from: FOLVar | FOLConst, l: Int): FOLFormula = l match {
      case 0 => Eq(from, const(to))
      case n => {
        val v = FOLVar(s"v_$n")
        fof"?$v (E($from, $v) & ${pathFrom(v, l - 1)})"
      }
    }

    pathFrom(const(from), length)
  }

  def graph(size: Int, edges: (Int, Int)*): Set[HOLClause] = {
    require(size >= 0, "size of graph must be non-negative")
    for (from, to) <- edges do
      require(1 <= from && from <= size, s"edge ($from, $to) starting point is not in range [1, $size]")
      require(1 <= to && to <= size, s"edge ($from, $to) end point is not in range [1, $size]")

    val constants = (1 to size).map(i => Const(s"a_$i", Ti))
    def a(i: Int): Const = constants(i - 1)

    val exhaustiveness = HOLClause(Iterable.empty, constants.map(c => Eq(c, fov"u")))
    val distinctness =
      for
        i <- 1 to size
        j <- 1 until i
      yield HOLClause(Seq(Eq(a(i), a(j))), Iterable.empty)
    val edgesAndNonEdges =
      for
        i <- 1 to size
        j <- 1 to size
      yield
        val polarity = Polarity(edges.contains((i, j)))
        HOLClause(Seq((Atom(le"E:i>i>o", a(i), a(j)), polarity)))

    (distinctness ++ edgesAndNonEdges :+ exhaustiveness).toSet
  }

  def apply(size: Int, mustContain: Int, mustAvoid: Int, edges: (Int, Int)*): ClauseSetPredicateEliminationProblem = {
    val constants = (1 to size).map(i => Const(s"a_$i", Ti))
    def a(i: Int): Const = constants(i - 1)

    val graphTheory = graph(size, edges*)
    val contain = hcl":- X(${a(mustContain)})"
    val avoid = hcl"X(${a(mustAvoid)}) :-"
    val edgeClosure = hcl"X(u), E(u,v) :- X(v)"

    ClauseSetPredicateEliminationProblem(
      Seq(hov"X:i>o"),
      graphTheory + contain + avoid + edgeClosure
    )
  }
}
