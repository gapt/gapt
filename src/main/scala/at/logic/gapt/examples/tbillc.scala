package at.logic.gapt.examples

import at.logic.gapt.expr.FOLAtom
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.proofs.{ Suc, Ant }
import at.logic.gapt.proofs.lk._

/**
 * This is an example used in the talk[1] at TbiLLC 2013. It generates a (cut-free) LK proof where the extracted
 * expansion tree has nested quantifiers.
 *
 * [1] http://www.illc.uva.nl/Tbilisi/Tbilisi2013/uploaded_files/inlineitem/riener.pdf
 */
object tbillc {
  // FIXME: Can the parser return this as an atom?
  val pa = Prover9TermParserLadrStyle.parseFormula( "P(a)" ).asInstanceOf[FOLAtom]
  val expxqxy = Prover9TermParserLadrStyle.parseFormula( "(exists x (P(x) & (exists y Q(x,y))))" )
  val qfa = Prover9TermParserLadrStyle.parseFormula( "Q(a,f(a))" ).asInstanceOf[FOLAtom]
  val qay = Prover9TermParserLadrStyle.parseFormula( "(exists y Q(a,y))" )
  val qga = Prover9TermParserLadrStyle.parseFormula( "Q(a,g(a))" ).asInstanceOf[FOLAtom]
  val a = Prover9TermParserLadrStyle.parseTerm( "a" )
  val fa = Prover9TermParserLadrStyle.parseTerm( "f(a)" )
  val ga = Prover9TermParserLadrStyle.parseTerm( "g(a)" )

  val pb = Prover9TermParserLadrStyle.parseFormula( "P(b)" ).asInstanceOf[FOLAtom]
  val qfb = Prover9TermParserLadrStyle.parseFormula( "Q(b,f(b))" ).asInstanceOf[FOLAtom]
  val qby = Prover9TermParserLadrStyle.parseFormula( "(exists y Q(b,y))" )
  val qgb = Prover9TermParserLadrStyle.parseFormula( "Q(b,g(b))" ).asInstanceOf[FOLAtom]
  val b = Prover9TermParserLadrStyle.parseTerm( "b" )
  val fb = Prover9TermParserLadrStyle.parseTerm( "f(b)" )
  val gb = Prover9TermParserLadrStyle.parseTerm( "g(b)" )

  val allpab = Prover9TermParserLadrStyle.parseFormula( "(all x (Q(x, f(x)) | Q(x, g(x))))" )
  val ta = Prover9TermParserLadrStyle.parseTerm( "a" )
  val tb = Prover9TermParserLadrStyle.parseTerm( "b" )

  def proofA: LKProof = {
    val a1 = LogicalAxiom( pa )
    val a2 = LogicalAxiom( qfa )
    val r2 = ExistsRightRule( a2, qay, fa )

    val a3 = LogicalAxiom( qga )
    val r3 = ExistsRightRule( a3, qay, ga )

    val r4 = OrLeftRule( r2, Ant( 0 ), r3, Ant( 0 ) )
    val r5 = ContractionRightRule( r4, qay )

    val r6 = AndRightRule( a1, pa, r5, qay )
    val r7 = ExistsRightRule( r6, expxqxy, a )
    r7
  }

  def proofB: LKProof = {
    val a1 = LogicalAxiom( pb )
    val a2 = LogicalAxiom( qfb )
    val r2 = ExistsRightRule( a2, qby, fb )

    val a3 = LogicalAxiom( qgb )
    val r3 = ExistsRightRule( a3, qby, gb )

    val r4 = OrLeftRule( r2, Ant( 0 ), r3, Ant( 0 ) )
    val r5 = ContractionRightRule( r4, qby )

    val r6 = AndRightRule( a1, pb, r5, qby )
    val r7 = ExistsRightRule( r6, expxqxy, b )
    r7
  }

  def apply() = {
    val a: LKProof = proofA
    val b: LKProof = proofB

    //val x = (SimpleFOLParser.term "x").asInstanceOf[FOLVar]

    val r1 = OrLeftRule( a, pa, b, pb )
    val r2 = ForallLeftRule( r1, allpab, ta )
    val r3 = ForallLeftRule( r2, allpab, tb )
    val r4 = ContractionMacroRule( r3 )
    r4
  }

}
