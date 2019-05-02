package gapt.proofs.hoare

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.Utils.numeral
import gapt.expr.subst.FOLSubstitution
import gapt.proofs.HOLSequent

object unrollLoop {
  def apply( p: Program, actualN: Int ): Program = p match {
    case ForLoop( i, n, b ) => Sequence(
      ( 0 until actualN ).map( actualI =>
        substVariables( b, Map( i -> numeral( actualI ), n -> numeral( actualN ) ) ) ) )
  }
}

case class SimpleInductionProblem( gamma: Seq[FOLFormula], alphaVar: FOLVar, B: FOLFormula ) {
  def sequent = HOLSequent( gamma, List( B ) )

  def instanceSequent( n: Int ) = {
    val instSubst = FOLSubstitution( alphaVar, numeral( n ) )
    HOLSequent( gamma map ( instSubst( _ ) ), List( instSubst( B ) ) )
  }
}

case class SimpleLoopProblem( loop: ForLoop, gamma: Seq[FOLFormula], precondition: FOLFormula, postcondition: FOLFormula ) {
  val programVariables = usedVariables( loop.body ).distinct diff List( loop.indexVar, loop.limit )

  def stateFunctionSymbol( programVariable: FOLVar ): String = programVariable match { case FOLVar( sym ) => s"sigma_$sym" }

  def varsAtTime( i: FOLTerm ): List[( FOLVar, FOLTerm )] =
    programVariables map { v => v -> FOLFunction( stateFunctionSymbol( v ), List( i ) ) }

  def pi: FOLFormula =
    FOLSubstitution( varsAtTime( loop.indexVar ) )(
      weakestPrecondition(
        loop.body,
        And( varsAtTime( FOLFunction( "s", List( loop.indexVar ) ) ) map {
          case ( v, s ) => Eq( s, v )
        } ) ) )

  def Pi: FOLFormula = All( loop.indexVar, pi )

  def A: FOLFormula = FOLSubstitution( varsAtTime( numeral( 0 ) ) )( precondition )
  def B: FOLFormula = FOLSubstitution( varsAtTime( loop.limit ) )( postcondition )

  def associatedSip = SimpleInductionProblem( gamma ++ List( Pi, A ), loop.limit, B )

  // TODO: instantiate Pi
  def instanceSequent( n: Int ) = associatedSip.instanceSequent( n )
}
