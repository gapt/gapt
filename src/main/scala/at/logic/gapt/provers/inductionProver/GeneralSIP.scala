package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.FSequent

class GeneralSIP( val Gamma0: List[FOLFormula], val Gamma1: List[FOLFormula], val Gamma2: List[FOLFormula], val B: FOLFormula, val t: List[FOLTerm], val u: List[FOLTerm] ) {
  import GeneralSIP._

  require( List( alpha, beta ) contains freeVariables( Gamma0 ), "Gamma0 contains free variables other than α, β" )
  require( List( alpha, nu, gamma ) contains freeVariables( Gamma1 ), "Gamma1 contains free variables other than α, ν, γ" )
  require( List( alpha ) contains freeVariables( Gamma2 ), "Gamma2 contains free variables other than α" )
  require( List( alpha ) contains freeVariables( B ), "B contains free variables other than α" )

  require( List( alpha ) contains freeVariables( u ), "A term in u contains free variables other than α" )
  require( List( alpha, nu, gamma ) contains freeVariables( t ), "A term in t contains free variables other than α, ν, γ" )
}

object GeneralSIP {
  val zero = FOLConst( "0" )
  val alpha = FOLVar( "α" )
  val beta = FOLVar( "β" )
  val gamma = FOLVar( "γ" )
  val nu = FOLVar( "ν" )
  val snu = FOLFunction( "s", List( nu ) )

  val X = Var( "X", Ti -> Ti -> Ti -> To )
}

class SchematicSIP( Gamma0: List[FOLFormula], Gamma1: List[FOLFormula], Gamma2: List[FOLFormula], B: FOLFormula, t: List[FOLTerm], u: List[FOLTerm] ) extends GeneralSIP( Gamma0, Gamma1, Gamma2, B, t, u ) {
  import GeneralSIP._

  val Sequent0 = FSequent( Gamma0, List( HOLAtom( X, alpha, zero, beta ) ) )

  private val Xt = t map { HOLAtom( X, alpha, nu, _ ) }
  val Sequent1 = FSequent( Gamma1 ++ Xt, List( HOLAtom( X, alpha, snu, gamma ) ) )

  private val Xu = u map { HOLAtom( X, alpha, alpha, _ ) }
  val Sequent2 = FSequent( Gamma2 ++ Xu, List( B ) )
}

class SimpleInductionProof( Gamma0: List[FOLFormula], Gamma1: List[FOLFormula], Gamma2: List[FOLFormula], B: FOLFormula, t: List[FOLTerm], u: List[FOLTerm], val inductionFormula: FOLFormula ) extends GeneralSIP( Gamma0, Gamma1, Gamma2, B, t, u ) {
  import GeneralSIP._

  require( List( alpha, nu, gamma ) contains freeVariables( inductionFormula ), "inductionFormula contains free variables other than α, ν, γ" )
}