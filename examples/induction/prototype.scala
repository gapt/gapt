import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{Utils, FOLSubstitution}
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.grammars.findMinimalSipGrammar
import at.logic.gapt.proofs.expansionTrees.{extractInstances, minimalExpansionSequent, InstanceTermEncoding}
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.provers.inductionProver.GeneralSIP._
import at.logic.gapt.provers.maxsat.QMaxSAT
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver

val endSequent = FSequent(
  Seq("(all x (all y (s(x+y) = x+s(y))))",
    "(all x (x+0 = x))") map parseFormula,
  Seq(Eq(
    FOLFunction("+", FOLFunction("+", alpha, alpha), alpha),
    FOLFunction("+", alpha, FOLFunction("+", alpha, alpha)))))

var instanceProofs = (0 until 3) map { n =>
  val instanceSequent = FOLSubstitution(alpha -> Utils.numeral(n)).apply(endSequent)
  println(s"[n=$n] Proving $instanceSequent")
  n -> LKToExpansionProof(new Prover9Prover().getLKProof(instanceSequent).get)
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

instanceLanguages foreach { case (n,l) =>
  println(s"Instance language for n=$n:\n${l.map(_.toString).sorted.mkString("\n")}")
}

println("Finding grammar...")
val grammar = findMinimalSipGrammar(instanceLanguages, new QMaxSAT)
println(grammar)

(0 until 5) foreach { n =>
  val generatedInstanceSequent = FOLSubstitution(alpha -> Utils.numeral(n))(
    termEncoding.decodeToFSequent(grammar.instanceGrammar(n).language))
  println(s"Checking tautology of instance language for n=$n: "
    + new VeriTProver().isValid(generatedInstanceSequent))
//  generatedInstanceSequent.antecedent.map(_.toString).sorted foreach println
}
