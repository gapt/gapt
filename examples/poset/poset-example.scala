import at.logic.gapt.expr.hol.{CNFp, instantiate}
import at.logic.gapt.grammars.{recSchemToVTRATG, findMinimalVectGrammar, VectTratGrammar}
import at.logic.gapt.proofs.{Suc, Sequent}
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr._
import at.logic.gapt.cutintro._
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.maxsat.ExternalMaxSATSolver
import at.logic.gapt.provers.sat.Sat4j

val f = FOLFunctionConst("f", 2)
val Seq(u, v, w, x, y, z) = Seq("u", "v", "w", "x", "y", "z") map { FOLVar(_) }
val Seq(a, b, c) = Seq("a", "b", "c") map { FOLConst(_) }

val eqRefl = All(x, x === x)
val eqSymm = All(x, All(y, (x === y) --> (y === x)))
val eqTran = All(x, All(y, All(z, ((x === y) & (y === z)) --> (x === z))))
val eqFCongr = All(x, All(y, All(u, All(v, ((x===y) & (u===v)) --> (f(x,u) === f(y,v))))))

val fComm = All(x, All(y, f(x, y) === f(y, x)))
val fAssoc = All(x, All(y, All(z, f(f(x, y), z) === f(x, f(y, z)))))

val fAntiSym = ((f(u, v) === u) & (f(v, u) === v)) --> (u === v)
val fTrans = ((f(x, y) === x) & (f(y, z) === y)) --> (f(x, z) === x)

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
    :+ fTrans
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
  qed)

val pAntiSym = (ProofBuilder
  c solve.solvePropositional(
    (f(u, v) === f(v, u)) +:
    ((f(u, v) === u) --> (u === f(u, v))) +:
    (((u === f(u, v)) & (f(u, v) === f(v, u))) --> (u === f(v, u))) +:
    (((u === f(v, u)) & (f(v, u) === v)) --> (u === v)) +:
    Sequent()
    :+ fAntiSym
  ).get
  u (ForallLeftBlock(_, fComm, Seq(u, v)))
  u (ForallLeftBlock(_, eqSymm, Seq(f(u, v), u)))
  u (ForallLeftBlock(_, eqTran, Seq(u, f(u, v), f(v, u))))
  u (ForallLeftBlock(_, eqTran, Seq(u, f(v, u), v)))
  qed)

val cutf = All.Block(Seq(x,y,z), fTrans & Substitution(u->z, v->x)(fAntiSym))

val lhs = (ProofBuilder
  c pTrans
  c pAntiSym
  u applySubstitution(Substitution(u -> z, v -> x))
  b (AndRightRule(_, Suc(0), _, Suc(0)))
  u (ForallRightBlock(_, cutf, Seq(x,y,z)))
  u (ContractionMacroRule(_))
  qed)

val conc = ((f(a, b) === a) & (f(b, c) === b) & (f(c, a) === c)) --> ((a === b) & (b === c))

val rhs = (ProofBuilder
  c solve.solvePropositional(
    instantiate(cutf, Seq(b,c,a)) +:
    instantiate(cutf, Seq(c,a,b)) +:
    Sequent()
    :+ conc
  ).get
  u (ForallLeftBlock(_, cutf, Seq(b,c,a)))
  u (ForallLeftBlock(_, cutf, Seq(c,a,b)))
  u (ContractionMacroRule(_))
  qed)

// proof with cut
val pwc = CutRule(lhs, rhs, cutf)

val p = ReductiveCutElimination(pwc)
val (terms, encoding) = FOLInstanceTermEncoding(p)
terms foreach println

if (true) {
  val recSchem = extractRecSchem(pwc)
  println("Recursion scheme of proof:")
  println(recSchem)
  println(s"Size: ${recSchem.rules.size} rules")
  val encRecSchem = encoding encode recSchem
  val vtratg = recSchemToVTRATG(encRecSchem)
  val sehs = vtratgToSEHS(encoding, vtratg)
  val canSol = CutIntroduction.computeCanonicalSolution(sehs)
  val canEHS = ExtendedHerbrandSequent(sehs, canSol)
  val minSol = improveSolutionLK(canEHS, Sat4j, hasEquality = false)
  println("Automatically improved cut-formula for grammar extracted from proof:")
  println(minSol.cutFormulas.head)

  CutIntroduction.constructLKProof(minSol, hasEquality = false)
}


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
