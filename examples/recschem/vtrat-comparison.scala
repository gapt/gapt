import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr.hol.{toNNF, simplify, lcomp}
import at.logic.gapt.grammars._
import at.logic.gapt.provers.maxsat.bestAvailableMaxSatSolver
import at.logic.gapt.utils.time

val N = 13
val terms = (0 until N).map { i =>
  FOLFunction("r", Numeral(i), Numeral(N - i))
}.toSet

val A = FOLConst("A")
val B = FOLFunctionConst("B", 2)
val Seq(x, y, z) = Seq("x", "y", "z") map { FOLVar(_) }
val rst = RecSchemTemplate(A,
  A -> B(x, y),
  A -> z,
  B(x, y) -> z
)
val targets = terms.map(A -> _).toSet[(LambdaExpression,LambdaExpression)]
val nfRecSchem = rst.stableRecSchem(targets)

println(lcomp(simplify(toNNF((new RecSchemGenLangFormula(nfRecSchem))(targets)))))

val nfG = stableProofVectGrammar(terms, Seq(2))
println(lcomp(simplify(toNNF(new VectGrammarMinimizationFormula(nfG).coversLanguage(terms)))))

val minimized = time {
  minimizeRecursionScheme(nfRecSchem, targets, solver = bestAvailableMaxSatSolver)
}
println(minimized)
println(terms.toSet diff minimized.language)
println(recSchemToVTRATG(minimized))

val minG = time {
  minimizeVectGrammar(nfG, terms, bestAvailableMaxSatSolver)
}
println(minG)
