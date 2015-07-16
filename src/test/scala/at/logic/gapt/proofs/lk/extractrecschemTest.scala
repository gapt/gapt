package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }
import org.specs2.mutable._

class ExtractRecSchemTest extends Specification {
  "simple" in {
    val g0 = parseFormula( "P(c)" )
    val g1 = parseFormula( "(all y (P(y) -> P(f(y))))" )
    val g2 = parseFormula( "P(f(f(f(f(c)))))" )

    val p1 = solve.solvePropositional( HOLSequent(
      Seq( "P(x) -> P(f(x))", "P(f(x)) -> P(f(f(x)))" ) map parseFormula,
      Seq( "P(x) -> P(f(f(x)))" ) map parseFormula
    ) ).get
    val cutf = parseFormula( "(all z (P(z) -> P(f(f(z)))))" )
    val p2 = ForallLeftRule( p1, parseFormula( "P(x) -> P(f(x))" ), g1, parseTerm( "x" ) )
    val p3 = ForallLeftRule( p2, parseFormula( "P(f(x)) -> P(f(f(x)))" ), g1, parseTerm( "f(x)" ) )
    val p4 = ContractionMacroRule( p3 )
    val p5 = ForallRightRule( p4, parseFormula( "P(x) -> P(f(f(x)))" ), cutf, FOLVar( "x" ) )

    val q1 = solve.solvePropositional( HOLSequent(
      Seq( "P(c) -> P(f(f(c)))", "P(f(f(c))) -> P(f(f(f(f(c)))))" ) map parseFormula,
      Seq( "P(c) -> P(f(f(f(f(c)))))" ) map parseFormula
    ) ).get
    val q2 = ForallLeftRule( q1, parseFormula( "P(c) -> P(f(f(c)))" ), cutf, parseTerm( "c" ) )
    val q3 = ForallLeftRule( q2, parseFormula( "P(f(f(c))) -> P(f(f(f(f(c)))))" ), cutf, parseTerm( "f(f(c))" ) )
    val q4 = ContractionMacroRule( q3 )

    val p = CutRule( p5, q4, cutf )

    val recSchem = extractRecSchem( p )
    val lang = recSchem.language( FOLConst( "A" ) )
    ok
  }
}