import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{Utils, FOLSubstitution}
import at.logic.gapt.expr.hol.{instantiate, univclosure}
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.formats.tip.TipParser
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.provers.inductionProver.SimpleInductionProof._
import at.logic.gapt.provers.inductionProver._
import org.apache.log4j.{Level, Logger}

import scala.io.Source

// doesn't work: associativity instances are too complicated
val assocES = FSequent(
  Seq("s(x+y) = x+s(y)", "x+0 = x")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("+", FOLFunction("+", alpha, alpha), alpha),
    FOLFunction("+", alpha, FOLFunction("+", alpha, alpha)))))

val commES = FSequent(
  Seq("s(x+y) = x+s(y)", "s(x+y) = s(x)+y", "x+0 = x", "0+x = x")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("+", FOLConst("k"), alpha),
    FOLFunction("+", alpha, FOLConst("k")))))

// doesn't work: associativity instances are too complicated
val factorialES = FSequent(
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
val homES = FSequent(
  Seq("f(s(x)) = s(f(x))",
    "0+x = x", "x+0 = x",
    "s(x)+y = s(x+y)", "x + s(y) = s(x+y)")
    map (s => univclosure(parseFormula(s))),
  Seq(Ex(FOLVar("x"), Eq(FOLFunction("+", FOLVar("x"), alpha), FOLFunction("f", alpha)))))

val generalES = FSequent(
  Seq("P(0,x)", "P(x,f(y)) & P(x,g(y)) -> P(s(x),y)")
    map (s => univclosure(parseFormula(s))),
  Seq(FOLAtom("P", alpha, FOLConst("c"))))

val generalDiffConclES = FSequent(
  Seq("P(0,x)", "P(x,f(y)) & P(x,g(y)) -> P(s(x),y)", "P(x,y) -> Q(x)")
    map (s => univclosure(parseFormula(s))),
  Seq(FOLAtom("Q", alpha)))

val linearES = FSequent(
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
lazy val tipES = TipParser.parse(Source.fromFile("/home/gebner/tip-benchs/benchmarks/isaplanner/prop_10.smt2").mkString) match {
  // the Imp-stripping is a workaround for issue 340
  case FSequent(theory, Seq(All(v, Imp(_, concl)))) =>
    FSequent(theory, Seq(Substitution(v -> alpha)(concl)))
}

val sumES = FSequent(
  List(
    FOLAtom("P", List(alpha, FOLConst("0"))),
    univclosure(parseFormula("P(s(x),y) -> P(x,s(y))"))),
  List(
    FOLAtom("P", List(FOLConst("0"), alpha))
  )
)

// P(0,0), ∀x,y.(P(x,y) → P(s(x),y)), ∀x,y.(P(x,y) → P(x,s(y))) :- P(α,α)
val squareES = FSequent(
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
val commsxES = FSequent(
  List(
    "x+0=x",
    "x+s(y)=s(x+y)"
  ) map {s => univclosure(parseFormula(s))},
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("x+s(x)=s(x)+x"))
  )
)

// ∀x.x+0 = x, ∀x,y. x+s(y) = s(x+y) :- α+s(0) = s(0) + α
val comm1ES = FSequent(
  List(
    "x+0=x",
    "x+s(y)=s(x+y)"
  ) map {s => univclosure(parseFormula(s))},
  List(
    FOLSubstitution(FOLVar("x"),FOLVar("α"))(parseFormula("x+s(0)=s(0)+x"))
  )
)

val assoc2ES = FSequent(
  Seq("s(x+y) = x+s(y)", "x+0 = x")
    map (s => univclosure(parseFormula(s))),
  Seq(Eq(
    FOLFunction("+", FOLFunction("+", Utils.numeral(2), alpha), alpha),
    FOLFunction("+", Utils.numeral(2), FOLFunction("+", alpha, alpha)))))

val evenES = FSequent(
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


val endSequent = commES

println(s"Proving $endSequent")

Logger.getLogger(classOf[SipProver].getName).setLevel(Level.DEBUG)

val sipProver = new SipProver(solutionFinder = new HeuristicSolutionFinder(0), instances = 0 until 3)

val maybeIndProof = sipProver.getSimpleInductionProof(endSequent)

maybeIndProof match {
  case Some(sip) =>
    println(s"Found induction proof with solution ${sip.inductionFormula}")
  case None =>
    println(s"Didn't find induction proof.")
}
