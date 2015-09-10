package at.logic.gapt.examples

import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.provers.prover9.Prover9Prover

object Pi2Pigeonhole {
  def zero = FOLConst( "0" )
  def one = FOLFunction( "s", zero )

  def T: FOLFormula = parseFormula( "(exists x (exists y (s(x) <= y & f(x) = f(y))))" )
  def I( i: FOLTerm ): FOLFormula = FOLSubstitution( FOLVar( "z" ) -> i )( parseFormula(
    "(all x (exists y (x <= y & f(y) = z)))"
  ) )
  def Gamma = HOLSequent( Seq(
    "(all x (all y (x <= M(x,y) & y <= M(x,y))))",
    "(all x (f(x) = 0 | f(x) = s(0)))"
  ) map parseFormula, Seq() )
  def Delta = HOLSequent( Seq(
    "(all x (all y (s(x) <= y -> x <= y)))"
  ) map parseFormula, Seq() )

  def I( i: FOLTerm, s: FOLTerm ): FOLFormula = instantiate( I( i ), s )
  def I( i: FOLTerm, s: FOLTerm, t: FOLTerm ): FOLFormula = instantiate( I( i ), Seq( s, t ) )
  def T( s: FOLTerm, t: FOLTerm ): FOLFormula = instantiate( T, Seq( s, t ) )

  def alpha = FOLVar( "α" )
  def alphahat = FOLVar( "α^" )
  def beta = FOLVar( "β" )
  def betaprime = FOLVar( "β'" )
  def betahat = FOLVar( "β^" )
  def betahatprime = FOLVar( "β^'" )

  def Delta_T_I_i( i: FOLTerm, beta: FOLVar, betaprime: FOLVar, prover: Prover9Prover ): LKProof = {
    var Some( p ) = prover.getLKProof( I( i, zero, beta ) +:
      I( i, FOLFunction( "s", beta ), betaprime ) +:
      Delta :+
      T( beta, betaprime ) )
    p = ExistsRightBlock( p, T, Seq( beta, betaprime ) )
    p = ExistsLeftRule( p, I( i, FOLFunction( "s", beta ), betaprime ), I( i, FOLFunction( "s", beta ) ), betaprime )
    p = ForallLeftRule( p, I( i, FOLFunction( "s", beta ) ), I( i ), FOLFunction( "s", beta ) )
    p = ExistsLeftRule( p, I( i, zero, beta ), I( i, zero ), beta )
    p = ForallLeftRule( p, I( i, zero ), I( i ), zero )
    p = ContractionMacroRule( p )
    p
  }

  def apply(): LKProof = {
    val prover = new Prover9Prover

    var Some( p1 ) = prover.getLKProof( Gamma :+
      I( zero, alpha, FOLFunction( "M", alpha, alphahat ) ) :+
      I( one, alphahat, FOLFunction( "M", alpha, alphahat ) ) )
    p1 = ExistsRightRule( p1, I( zero, alpha, FOLFunction( "M", alpha, alphahat ) ), I( zero, alpha ),
      FOLFunction( "M", alpha, alphahat ) )
    p1 = ExistsRightRule( p1, I( one, alphahat, FOLFunction( "M", alpha, alphahat ) ), I( one, alphahat ),
      FOLFunction( "M", alpha, alphahat ) )
    p1 = ForallRightRule( p1, I( one, alphahat ), I( one ), alphahat )

    val p2 = Delta_T_I_i( one, betahat, betahatprime, prover )

    var p3 = CutRule( p1, p2, I( one ) ).asInstanceOf[LKProof]
    p3 = ForallRightRule( p3, I( zero, alpha ), I( zero ), alpha )

    val p4 = Delta_T_I_i( zero, beta, betaprime, prover )

    val p5 = CutRule( p3, p4, I( zero ) ).asInstanceOf[LKProof]

    ContractionMacroRule( p5 )
  }
}
