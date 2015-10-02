import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr.hol.{toNNF, simplify, lcomp}
import at.logic.gapt.grammars._
import at.logic.gapt.provers.maxsat.bestAvailableMaxSatSolver
import at.logic.gapt.utils.time

val N = 8
val terms = (0 until N).map { i =>
  FOLFunction("r", Numeral(i), Numeral(N - i))
}.toSet

val A = FOLConst("A")
val B = FOLFunctionHead("B", 2)
val Seq(x, y, z) = Seq("x", "y", "z") map {
  FOLVar(_)
}
val rst = RecSchemTemplate(A, Set(A -> B(x, y).asInstanceOf[FOLTerm], B(x, y).asInstanceOf[FOLTerm] -> z))
val targets = terms.map(A.asInstanceOf[FOLTerm] -> _)
val nfRecSchem = rst.normalFormRecSchem(targets)

println(lcomp(simplify(toNNF((new RecSchemGenLangFormula(nfRecSchem))(targets)))))

val nfG = normalFormsProofVectGrammar(terms, Seq(2))
println(lcomp(simplify(toNNF(new VectGrammarMinimizationFormula(nfG).coversLanguage(terms)))))

val minimized = time {
  minimizeRecursionScheme(nfRecSchem, targets, solver = bestAvailableMaxSatSolver)
}
println(minimized)
println(terms.toSet diff minimized.language)

val minG = time {
  minimizeVectGrammar(nfG, terms, bestAvailableMaxSatSolver)
}
println(minG)
