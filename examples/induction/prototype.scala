import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{reduceHolToFol, Utils, FOLSubstitution}
import at.logic.gapt.expr.hol.{instantiate, univclosure}
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.{Sequent, HOLSequent}
import at.logic.gapt.provers.inductionProver.SimpleInductionProof._
import at.logic.gapt.provers.inductionProver._
import org.apache.log4j.{Level, Logger}

import scala.io.Source

// doesn't work: associativity instances are too complicated
val assocES = HOLSequent(
  Seq("s(x+y) = x+s(y)", "x+0 = x")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("+", FOLFunction("+", alpha, alpha), alpha),
    FOLFunction("+", alpha, FOLFunction("+", alpha, alpha)))))

val commES = HOLSequent(
  Seq("s(x+y) = x+s(y)", "s(x+y) = s(x)+y", "x+0 = x", "0+x = x")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("+", FOLConst("k"), alpha),
    FOLFunction("+", alpha, FOLConst("k")))))

// doesn't work: associativity instances are too complicated
val factorialES = HOLSequent(
  Seq(
    "f(0) = 1",
    "s(x)*f(x) = f(s(x))",
    "g(x,0) = x",
    "g(x*s(y),y) = g(x,s(y))",
    "x*1 = x",
    "1*x = x",
    "(x*y)*z = x*(y*z)")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("g", FOLConst("1"), alpha),
    FOLFunction("f", alpha))))

// doesn't work: seems to require Sigma_1-induction
val homES = HOLSequent(
  Seq("f(s(x)) = s(f(x))",
    "0+x = x", "x+0 = x",
    "s(x)+y = s(x+y)", "x + s(y) = s(x+y)")
    map (s => univclosure(parseFormula(s))),
  Seq(Ex(FOLVar("x"), Eq(FOLFunction("+", FOLVar("x"), alpha), FOLFunction("f", alpha)))))

val generalES = HOLSequent(
  Seq("P(0,x)", "P(x,f(y)) & P(x,g(y)) -> P(s(x),y)")
    map (s => univclosure(parseFormula(s))),
  Seq(FOLAtom("P", alpha, FOLConst("c"))))

val generalDiffConclES = HOLSequent(
  Seq("P(0,x)", "P(x,f(y)) & P(x,g(y)) -> P(s(x),y)", "P(x,y) -> Q(x)")
    map (s => univclosure(parseFormula(s))),
  Seq(FOLAtom("Q", alpha)))

val linearES = HOLSequent(
  Seq("P(x) -> P(s(x))", "P(0)")
    map (s => univclosure(parseFormula(s))),
  Seq(FOLAtom("P", alpha)))

// known to be working:
//   isaplanner/prop_10.smt2
//   isaplanner/prop_17.smt2
//   tip2015/nat_pow_one.smt2
//
// interesting failures:
//   prod/prop_16.smt2
lazy val tipES = reduceHolToFol(TipSmtParser.parseFile("/home/gebner/tip-benchs/benchmarks/isaplanner/prop_10.smt2").toSequent) match {
  case Sequent(theory, Seq(All(v, concl))) =>
    val repl = Map[LambdaExpression,LambdaExpression](FOLConst("Z") -> FOLConst("0"), FOLFunctionConst("S",1) -> FOLFunctionConst("s",1))
    reduceHolToFol(Sequent(theory, Seq(Substitution(v -> alpha)(concl)))) map { TermReplacement(_, repl) }
}

val sumES = HOLSequent(
  List(
    FOLAtom("P", List(alpha, FOLConst("0"))),
    univclosure(parseFormula("P(s(x),y) -> P(x,s(y))"))),
  List(
    FOLAtom("P", List(FOLConst("0"), alpha))
  )
)

// P(0,0), ∀x,y.(P(x,y) → P(s(x),y)), ∀x,y.(P(x,y) → P(x,s(y))) :- P(α,α)
val squareES = HOLSequent(
  List(
    "P(0,0)",
    "P(x,y) -> P(s(x),y)",
    "P(x,y) -> P(x,s(y))"
  ) map {s => univclosure(parseFormula(s))},
  List(
    FOLAtom("P", List(FOLVar("α"), FOLVar("α")))
  )
)

// ∀x.x+0 = x, ∀x,y. x+s(y) = s(x+y) :- α+s(α) = s(α) + α
val commsxES = HOLSequent(
  List(
    "x+0=x",
    "x+s(y)=s(x+y)"
  ) map {s => univclosure(parseFormula(s))},
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("x+s(x)=s(x)+x"))
  )
)

// ∀x.x+0 = x, ∀x,y. x+s(y) = s(x+y) :- α+s(0) = s(0) + α
val comm1ES = HOLSequent(
  List(
    "x+0=x",
    "x+s(y)=s(x+y)"
  ) map {s => univclosure(parseFormula(s))},
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("x+s(0)=s(0)+x"))
  )
)

val assoc2ES = HOLSequent(
  Seq("s(x+y) = x+s(y)", "x+0 = x")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("+", FOLFunction("+", Utils.numeral(2), alpha), alpha),
    FOLFunction("+", Utils.numeral(2), FOLFunction("+", alpha, alpha)))))

val evenES = HOLSequent(
  List(
    "x+s(y) = s(x+y)",
    "x+0 = x",
    "even(0)",
    "-even(s(0))",
    "even(s(s(x))) <-> even(x)"
  ) map (s => univclosure(parseFormula(s))),
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("even(x+x)"))
  )
)

// TODO: should be solvable with Q(y) <-> P(y) <-> -P(s(y))
val twoEvenDefsES = HOLSequent(
  List(
    "P(0)", "-P(s(0))", "P(s(s(x))) <-> P(x)",
    "Q(0)", "Q(s(x)) <-> -Q(x)"
  ) map (s => univclosure(parseFormula(s))),
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("P(x) <-> Q(x)"))
  )
)

val twoPlusDefsES = HOLSequent(
  List(
    "x+s(y) = s(x+y)", "x+0 = x",
    "s(x)*y = s(x*y)", "0*x = x"
  ) map (s => univclosure(parseFormula(s))),
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("x+x = x*x"))
  )
)

val minusES = HOLSequent(List(
  "p(0) = 0",
  "x-s(y) = p(x-y)",
  "x - 0 = x"
) map {s => univclosure(parseFormula(s))},
  List(
    FOLSubstitution(FOLVar("x"),alpha)(parseFormula("0 - x = 0")))
    )

val endSequent = tipES

println(s"Proving $endSequent")

Logger.getLogger(classOf[SipProver].getName).setLevel(Level.DEBUG)

val sipProver = new SipProver(solutionFinder = new HeuristicSolutionFinder(1), instances = 0 until 3)

val maybeIndProof = sipProver.getSimpleInductionProof(endSequent)

maybeIndProof match {
  case Some(sip) =>
    println(s"Found induction proof with solution ${sip.inductionFormula}")
  case None =>
    println(s"Didn't find induction proof.")
}
