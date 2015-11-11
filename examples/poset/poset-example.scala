import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.grammars.{findMinimalVectGrammar, VectTratGrammar}
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.expr._
import at.logic.gapt.cutintro.{GrammarFindingMethod, MaxSATMethod, CutIntroduction}
import at.logic.gapt.provers.maxsat.ExternalMaxSATSolver

val f = FOLFunctionConst("f", 2)
val Seq(u, v, w, x, y, z) = Seq("u", "v", "w", "x", "y", "z") map { FOLVar(_) }
val Seq(a, b, c) = Seq("a", "b", "c") map { FOLConst(_) }

val eqRefl = All(x, x === x)
val eqSymm = All(x, All(y, (x === y) --> (y === x)))
val eqTran = All(x, All(y, All(z, ((x === y) & (y === z)) --> (x === z))))
val eqFCongr = All(x, All(y, All(u, All(v, ((x===y) & (u===v)) --> (f(x,u) === f(y,v))))))

val fComm = All(x, All(y, f(x, y) === f(y, x)))
val fAssoc = All(x, All(y, All(z, f(f(x, y), z) === f(x, f(y, z)))))

val fAntiSym = All(u, All(v, ((f(u, v) === u) & (f(v, u) === v)) --> (u === v)))
val fTrans = All(x, All(y, All(z, ((f(x, y) === x) & (f(y, z) === y)) --> (f(x, z) === x))))

val pTrans = (ProofBuilder
  c solve.solvePropositional(
    (z === z) +:
    (((f(x, y) === x) & (z === z)) --> (f(f(x, y), z) === f(x, z))) +:
    ((f(f(x, y), z) === f(x, z)) --> (f(x, z) === f(f(x, y), z))) +:

    (f(f(x, y), z) === f(x, f(y, z))) +:

    (x === x) +:
    (((x === x) & (f(y, z) === y)) --> (f(x, f(y, z)) === f(x, y))) +:

    (((f(x, z) === f(f(x, y), z)) & (f(f(x, y), z) === f(x, f(y, z)))) --> (f(x, z) === f(x, f(y, z)))) +:
    (((f(x, z) === f(x, f(y, z))) & (f(x, f(y, z)) === f(x, y))) --> (f(x, z) === f(x, y))) +:
    (((f(x, z) === f(x, y)) & (f(x, y) === x)) --> (f(x, z) === x)) +:
    Sequent()
    :+ instantiate(fTrans, Seq(x, y, z))
  ).get
  u (ForallLeftBlock(_, eqRefl, Seq(x)))
  u (ForallLeftBlock(_, eqRefl, Seq(z)))
  u (ForallLeftBlock(_, eqSymm, Seq(f(f(x, y), z), f(x, z))))
  u (ForallLeftBlock(_, eqTran, Seq(f(x, z), f(f(x, y), z), f(x, f(y, z)))))
  u (ForallLeftBlock(_, eqTran, Seq(f(x, z), f(x, f(y, z)), f(x, y))))
  u (ForallLeftBlock(_, eqTran, Seq(f(x, z), f(x, y), x)))
  u (ForallLeftBlock(_, eqFCongr, Seq(f(x, y), x, z, z)))
  u (ForallLeftBlock(_, eqFCongr, Seq(x, x, f(y, z), y)))
  u (ForallLeftBlock(_, fAssoc, Seq(x, y, z)))
  u (ForallRightBlock(_, fTrans, Seq(x, y, z)))
  qed)

val pAntiSym = (ProofBuilder
  c solve.solvePropositional(
    (f(u, v) === f(v, u)) +:
    ((f(u, v) === u) --> (u === f(u, v))) +:
    (((u === f(u, v)) & (f(u, v) === f(v, u))) --> (u === f(v, u))) +:
    (((u === f(v, u)) & (f(v, u) === v)) --> (u === v)) +:
    Sequent()
    :+ instantiate(fAntiSym, Seq(u, v))
  ).get
  u (ForallLeftBlock(_, fComm, Seq(u, v)))
  u (ForallLeftBlock(_, eqSymm, Seq(f(u, v), u)))
  u (ForallLeftBlock(_, eqTran, Seq(u, f(u, v), f(v, u))))
  u (ForallLeftBlock(_, eqTran, Seq(u, f(v, u), v)))
  u (ForallRightBlock(_, fAntiSym, Seq(u, v)))
  qed)

val lhs = ContractionMacroRule(AndRightRule(pAntiSym, fAntiSym, pTrans, fTrans))

val rhs = {
  val EAS = formulaToExpansionTree(fAntiSym, List(Substitution(u -> a, v -> b), Substitution(u -> b, v -> c)), false)
  val ETpo = formulaToExpansionTree(fTrans, List(Substitution(x -> b, y -> c, z -> a), Substitution(x -> c, y -> a, z -> b)), false)

  val ETcut = ETAnd(EAS, ETpo)
  val conc = ((f(a, b) === a) & (f(b, c) === b) & (f(c, a) === c)) --> ((a === b) & (b === c))
  val Econc = formulaToExpansionTree(conc, true)

  ExpansionProofToLK(ETcut +: Sequent() :+ Econc)
}

// proof with cut
val pwc = CutRule(lhs, rhs, fAntiSym & fTrans)

val p = ReductiveCutElimination(pwc)
val (terms, encoding) = FOLInstanceTermEncoding(p)
println(terms)

CutIntroduction.compressLKProof(p,
  method = new GrammarFindingMethod {
    override def findGrammars(lang: Set[FOLTerm]): Option[VectTratGrammar] = {
      Some(findMinimalVectGrammar(lang, Seq(3),
        maxSATSolver = new ExternalMaxSATSolver("open-wbo", "-cpu-lim=100", "-algorithm=1"),
        weight = _._1.size))
    }

    override def name = "wmaxsat_3"
  },
  verbose = true)
