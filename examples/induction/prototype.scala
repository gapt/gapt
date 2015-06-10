import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.provers.inductionProver.SimpleInductionProof._
import at.logic.gapt.provers.inductionProver._
import org.apache.log4j.{Level, Logger}

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

val endSequent = linearES

println(s"Proving $endSequent")

Logger.getLogger(classOf[SipProver].getName).setLevel(Level.DEBUG)

// TODO: just a stop-gap
val solutionCandidates = Seq(
  "P(x,y)",
  "P(0) -> P(x)",
  "y+x = x+y"
) map(s => FOLSubstitution(
  FOLVar("x") -> SimpleInductionProof.nu,
  FOLVar("y") -> SimpleInductionProof.gamma,
  FOLVar("z") -> SimpleInductionProof.alpha)(parseFormula(s)))
val solutionFinder = new SolutionFinder {
  override def findSolution(schematicSip: SimpleInductionProof): Option[FOLFormula] =
    solutionCandidates find { cand =>
      try {
        schematicSip.solve(cand).toLKProof
        true
      } catch {
        case _: Throwable => false
      }
    }
}

val sipProver = new SipProver(solutionFinder)

val maybeIndProof = sipProver.getLKProofAndSolution(endSequent)

maybeIndProof match {
  case Some((indProof, solution)) =>
    println(s"Found induction proof with solution $solution")
  case None =>
    println(s"Didn't find induction proof.")
}
