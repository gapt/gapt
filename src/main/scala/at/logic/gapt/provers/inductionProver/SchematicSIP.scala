package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._

class SchematicSIP (val Gamma0: List[FOLFormula], val Gamma1: List[FOLFormula], val Gamma2: List[FOLFormula], val B: FOLFormula, val t: List[FOLTerm], val u: List[FOLTerm]) {
  import SchematicSIP._

  require(List(alpha, beta) contains freeVariables(Gamma0), "Gamma0 contains free variables other than α, β")
  require(List(alpha, nu, gamma) contains freeVariables(Gamma1), "Gamma1 contains free variables other than α, ν, γ")
  require(List(alpha) contains freeVariables(Gamma2), "Gamma2 contains free variables other than α")
  require(List(alpha) contains freeVariables(B), "Gamma2 contains free variables other than α")
}

object SchematicSIP {
  val alpha = FOLVar("α")
  val beta = FOLVar("β")
  val gamma = FOLVar("γ")
  val nu = FOLVar("ν")
  val snu = FOLFunction("s", List(nu))

  val X = Var("X", Ti->Ti->Ti->To)
}