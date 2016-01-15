package at.logic.gapt.examples

import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr.{ FOLConst, FOLVar }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base.LKProof

object equation_example {
  def apply: ( LKProof, FOLSubstitution ) = {
    val List(
      uv, fuu, fuv, ab, fab ) = List(
      "u = v",
      "f(u)=f(u)", "f(u)=f(v)", "a=b", "f(a)=f(b)"
    ) map ( Prover9TermParserLadrStyle.parseFormula )
    val List( uy, xy, ay ) = List(
      "(all y (u = y -> f(u) = f(y)))",
      "(all x all y (x = y -> f(x) = f(y)))",
      "(all y (a = y -> f(a) = f(y)))"
    ) map ( Prover9TermParserLadrStyle
        .parseFormula )
    val List( u, v ) = List( "u", "v" ).map( s => FOLVar( s ) )

    val List( a, b ) = List( "a", "b" ).map( s => FOLConst( s ) )
    val ax1 = Axiom( List( uv ), List( uv ) )
    val ax2 = Axiom( List(), List( fuu ) )
    val ax3 = Axiom( List( ab ), List( ab ) )
    val ax4 = Axiom( List( fab ), List( fab ) )

    val i1 = EquationRight1Rule( ax1, ax2, ax1.root.succedent( 0 ), ax2.root.succedent( 0 ), fuv )

    val i2 = ImpRightRule( i1, i1.root.antecedent( 0 ), i1.root.succedent( 0 ) )
    println( i2.root )
    val i3 = ForallRightRule( i2, i2.root.succedent( 0 ), uy, v )
    val i4 = ForallRightRule( i3, i3.root.succedent( 0 ), xy, u )

    val i5 = ImpLeftRule( ax3, ax4, ax3.root.succedent( 0 ), ax4.root.antecedent( 0 ) )
    val i6 = ForallLeftRule( i5, i5.root.antecedent( 1 ), ay, b )
    val i7 = ForallLeftRule( i6, i6.root.antecedent( 1 ), xy, a )

    val es = CutRule( i4, i7, i4.root.succedent( 0 ), i7.root.antecedent( 1 ) )
    val sub = FOLSubstitution( ( u, b ) :: Nil )
    ( es, sub )
  }
}
