import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.expr._
import at.logic.gapt.cutintro.{MaxSATMethod, CutIntroduction}
import at.logic.gapt.provers.maxsat.ExternalMaxSATSolver
import at.logic.gapt.provers.veriT.VeriT

val f = FOLFunctionHead("f", 2)
val Seq(u, v, w, x, y, z) = Seq("u", "v", "w", "x", "y", "z") map { FOLVar(_) }
val Seq(a, b, c) = Seq("a", "b", "c") map { FOLConst(_) }

val C = All(x, All(y, f(x, y) === f(y, x)))
val AS = All(u, All(v, (f(u, v) === u) --> ((f(v, u) === v) --> (u === v))))

val A = All(x, All(y, All(z, f(f(x, y), z) === f(x, f(y, z)))))
val Tpo = All(x, All(y, All(z, (f(x, y) === x) --> ((f(y, z) === y) --> (f(x, z) === x)))))

val trans = {
  val A0 = instantiate(A, Seq(u, v, w))
  val T0 = instantiate(Tpo, Seq(u, v, w))

  val Some(e) = VeriT.getExpansionSequent(A0 +: Sequent() :+ T0)

  (ProofBuilder
    c ExpansionProofToLK(e)
    u (ForallLeftBlock(_, A, Seq(u, v, w)))
    u (ForallRightBlock(_, Tpo, Seq(u, v, w)))
    qed)
}

val antisymm = {
  val C0 = instantiate(C, Seq(u, v))
  val AS0 = instantiate(AS, Seq(u, v))

  val Some(e) = VeriT.getExpansionSequent(C0 +: Sequent() :+ AS0)

  (ProofBuilder
    c ExpansionProofToLK(e)
    u (ForallLeftBlock(_, C, Seq(u, v)))
    u (ForallRightBlock(_, AS, Seq(u, v)))
    qed)
}

val lhs = ContractionMacroRule(AndRightRule(antisymm, AS, trans, Tpo))

val rhs = {
  //val AS1 = parseFormula( "( f(a,b)=a -> ( f(b,a)=b -> a=b ))" )
  //val AS2 = parseFormula( "( f(b,c)=b -> ( f(c,b)=c -> b=c ))" )
  val EAS = formulaToExpansionTree(AS, List(Substitution(u -> a, v -> b), Substitution(u -> b, v -> c)), false)

  //val Tpo1 = parseFormula( "( f(b,c)=b -> ( f(c,a)=c -> f(b,a)=b ))" )
  //val Tpo2 = parseFormula( "( f(c,a)=c -> ( f(a,b)=a -> f(c,b)=c ))" )
  val ETpo = formulaToExpansionTree(Tpo, List(Substitution(x -> b, y -> c, z -> a), Substitution(x -> c, y -> a, z -> b)), false)

  val ETcut = ETAnd(EAS, ETpo)
  val conc = ((f(a, b) === a) & (f(b, c) === b) & (f(c, a) === c)) --> ((a === b) & (b === c))
  val Econc = formulaToExpansionTree(conc, true)

  ExpansionProofToLK(ETcut +: Sequent() :+ Econc)
}

// proof with cut
val pwc = CutRule(lhs, rhs, And(AS, Tpo))

val p = ReductiveCutElimination(pwc)
val (terms, encoding) = FOLInstanceTermEncoding(p)
println(terms)

// This does not work, even running it for 2 days produces only a grammar of size 22.
if (false) CutIntroduction.compressLKProof(p,
  method = MaxSATMethod(new ExternalMaxSATSolver("open-wbo", "-cpu-lim=30", "-algorithm=1"), 3),
  verbose = true)
