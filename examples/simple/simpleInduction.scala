/*
import at.logic.calculi.lk._
import at.logic.language.fol._
import at.logic.language.hol.{HOLExpression, AllVarBlock}
import at.logic.language.fol.Substitution

object inductionExamples {

  val (x,y,z) = (FOLVar("x"), FOLVar("y"), FOLVar("z"))
  def S(x: FOLTerm) = Function("S", List(x))
  def plus(x: FOLTerm, y: FOLTerm) = Function("+", List(x,y))
  val zero = FOLConst("0")

  val assocXYZ = Equation(plus(plus(x,y),z), plus(x, plus(y,z)))
  val assocXY0 = Equation(plus(plus(x,y), zero), plus(x, plus(y, zero)))
  val assocXYSZ = Equation(plus(plus(x,y),S(z)), plus(x, plus(y,S(z))))

  val axAdd0 = AllVar(x, Equation(plus(x,zero), x))
  val axAddS = AllVarBlock(List(x,y),
    Equation(
      plus(x, S(y)),
      S(plus(x,y))))

  val leftSubProof =
    ForallLeftRule(Axiom(List(Equation(plus(plus(x,y),zero), plus(x,y))), List(Equation(plus(plus(x,y),zero), plus(x,y)))), 

}*/
