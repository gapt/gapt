package at.logic.gapt.examples

import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, HOLSequent }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.escargot.Escargot

object Pi2Pigeonhole {
  val zero = FOLConst( "0" )
  val s = FOLFunctionConst( "s", 1 )
  val one = s( zero )

  val M = FOLFunctionConst( "M", 2 )

  val f = FOLFunctionConst( "f", 1 )
  val lteq = FOLAtomConst( "<=", 2 )

  val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }

  val T = Ex( x, Ex( y, lteq( s( x ), y ) & Eq( f( x ), f( y ) ) ) )
  def I( i: LambdaExpression ): HOLFormula = All( x, Ex( y, lteq( x, y ) & Eq( f( y ), i ) ) )
  val Gamma =
    All( x, All( y, lteq( x, M( x, y ) ) & lteq( y, M( x, y ) ) ) ) +:
      All( x, Eq( f( x ), zero ) | Eq( f( x ), s( zero ) ) ) +: Sequent()
  val Delta = All( x, All( y, lteq( s( x ), y ) --> lteq( x, y ) ) ) +: Sequent()

  def I( i: LambdaExpression, s: LambdaExpression ): HOLFormula = instantiate( I( i ), s )
  def I( i: LambdaExpression, s: LambdaExpression, t: LambdaExpression ): HOLFormula = instantiate( I( i ), Seq( s, t ) )
  def T( s: LambdaExpression, t: LambdaExpression ): HOLFormula = instantiate( T, Seq( s, t ) )

  val alpha = FOLVar( "α" )
  val alphahat = FOLVar( "α^" )
  val beta = FOLVar( "β" )
  val betaprime = FOLVar( "β'" )
  val betahat = FOLVar( "β^" )
  val betahatprime = FOLVar( "β^'" )

  def Delta_T_I_i( i: LambdaExpression, beta: Var, betaprime: Var ): LKProof = {
    var Some( p ) = Escargot.getLKProof( I( i, zero, beta ) +:
      I( i, s( beta ), betaprime ) +:
      Delta :+
      T( beta, betaprime ) )
    p = ExistsRightBlock( p, T, Seq( beta, betaprime ) )
    p = ExistsLeftRule( p, I( i, s( beta ) ), betaprime )
    p = ForallLeftRule( p, I( i ), s( beta ) )
    p = ExistsLeftRule( p, I( i, zero ), beta )
    p = ForallLeftRule( p, I( i ), zero )
    p = ContractionMacroRule( p )
    p
  }

  def apply(): LKProof = {
    var Some( p1 ) = Escargot.getLKProof( Gamma :+
      I( zero, alpha, M( alpha, alphahat ) ) :+
      I( one, alphahat, M( alpha, alphahat ) ) )
    p1 = ExistsRightRule( p1, I( zero, alpha ), M( alpha, alphahat ) )
    p1 = ExistsRightRule( p1, I( one, alphahat ), M( alpha, alphahat ) )
    p1 = ForallRightRule( p1, I( one ), alphahat )

    val p2 = Delta_T_I_i( one, betahat, betahatprime )

    var p3: LKProof = CutRule( p1, p2, I( one ) )
    p3 = ForallRightRule( p3, I( zero ), alpha )

    val p4 = Delta_T_I_i( zero, beta, betaprime )

    val p5 = CutRule( p3, p4, I( zero ) )

    ContractionMacroRule( p5 )
  }
}
