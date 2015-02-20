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

  val eqXPYP0EXPY = Equation(plus(plus(x,y),zero), plus(x,y))
  val eqYP0EY = Equation(plus(y,zero), y)

  val axXPYP0EXPY = Axiom(List(eqXPYP0EXPY), List(eqXPYP0EXPY))
  val axYP0EY = Axiom(List(eqYP0EY), List(eqYP0EY))

  val refXPY = Axiom(Nil, List(Equation(plus(x,y),plus(x,y))))

  val inductionBaseL =
    ForallLeftRule(
      axXPYP0EXPY,
      eqXPYP0EXPY,
      axAdd0,
      plus(x,y))
  
  val inductionBaseRL =
    ForallLeftRule(
      axYP0EY,
      eqYP0EY,
      axAdd0,
      y)

  val inductionBaseR =
    EquationRightRule(
      inductionBaseRL,
      refXPY,
      eqYP0EY,
      Equation(plus(x,y),plus(x,y)),
      Equation(
         plus(x,y),
         plus(x,plus(y,zero))
      )
    )

  val inductionBase =
  ContractionMacroRule(
    EquationRightRule(
      inductionBaseL,
      inductionBaseR,
      eqXPYP0EXPY,
      Equation(
        plus(x,y),
        plus(x,plus(y,zero))
      ),
      Equation(
        plus(plus(x,y), zero),
        plus(x,plus(y,zero))
      )
    )
  )
}
