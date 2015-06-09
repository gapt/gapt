import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{Utils, FOLSubstitution}
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.grammars.findMinimalSipGrammar
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.resolution.CNFp
import at.logic.gapt.provers.inductionProver.GeneralSIP._
import at.logic.gapt.provers.inductionProver.{canonicalSolution, decodeSipGrammar}
import at.logic.gapt.provers.maxsat.QMaxSAT
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver

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

val endSequent = commES

var instanceProofs = (0 until 3) map { n =>
  val instanceSequent = FOLSubstitution(alpha -> Utils.numeral(n)).apply(endSequent)
  println(s"[n=$n] Proving $instanceSequent")
  n -> LKToExpansionProof(new Prover9Prover().getLKProof(instanceSequent).get)
}

// Ground the instance proofs.
instanceProofs = instanceProofs map { case (n, expProof) =>
  n -> substitute(
    FOLSubstitution(freeVariables(toDeep(expProof).toFormula).
      map { c => FOLVar(c.name) -> FOLConst(c.name) }.toSeq),
    expProof)
}

//instanceProofs = instanceProofs map { case (n, expProof) =>
//  val minExpProof = minimalExpansionSequent(expProof, new VeriTProver).get
//  val removedInstances = extractInstances(expProof) diff extractInstances(minExpProof)
//  println(s"[n=$n] Removing unnecessary instances $removedInstances")
//  n -> minExpProof
//}

val termEncoding = InstanceTermEncoding(endSequent)
val instanceLanguages = instanceProofs map { case (n, expSeq) =>
  n -> termEncoding.encode(expSeq)
}

instanceLanguages foreach { case (n, l) =>
  println(s"Instance language for n=$n:\n${l.map(_.toString).sorted.mkString("\n")}")
}

println("Finding grammar...")
val grammar = findMinimalSipGrammar(instanceLanguages, new QMaxSAT)
println(grammar)

(0 until 10) foreach { n =>
  val generatedInstanceSequent = FOLSubstitution(alpha -> Utils.numeral(n))(
    termEncoding.decodeToFSequent(grammar.instanceGrammar(n).language))
  println(s"Checking tautology of instance language for n=$n: "
    + new VeriTProver().isValid(generatedInstanceSequent))
  //  generatedInstanceSequent.antecedent.map(_.toString).sorted foreach println
}

val schematicSip = decodeSipGrammar(termEncoding, grammar)
println(s"Gamma0 = ${schematicSip.Gamma0}")
println(s"Gamma1 = ${schematicSip.Gamma1}")
println(s"Gamma2 = ${schematicSip.Gamma2}")
println(s"t = ${schematicSip.t}")
println(s"u = ${schematicSip.u}")

(0 until 3) foreach { i =>
  val C_i = canonicalSolution(schematicSip, i)
  val C_i_CNF = CNFp(C_i)
  println(s"C_$i = $C_i_CNF")
}
