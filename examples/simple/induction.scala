import at.logic.calculi.lk._
import at.logic.language.fol._
import at.logic.language.hol.{HOLExpression, AllVarBlock}
import at.logic.language.fol.Substitution

object inductionExamples {

  val (x,y,z) = (FOLVar("x"), FOLVar("y"), FOLVar("z"))
  val (a,b,c) = (FOLVar("α"), FOLVar("β"), FOLVar("γ"))
  def S(x: FOLTerm) = Function("S", List(x))
  def plus(x: FOLTerm, y: FOLTerm) = Function("+", List(x,y))
  val zero = FOLConst("0")

  val assoc = AllVarBlock(List(x,y,z), Equation(plus(plus(x,y),z), plus(x, plus(y,z)))).asInstanceOf[FOLFormula]
  val assocXYZ = Equation(plus(plus(a,b),c), plus(a, plus(b,c)))
  val assocXY0 = Equation(plus(plus(a,b), zero), plus(a, plus(b, zero)))
  val assocXYSZ = Equation(plus(plus(a,b),S(c)), plus(a, plus(b,S(c))))

  val axAdd0 = AllVar(x, Equation(plus(x,zero), x))
  val axAddS = AllVarBlock(List(x,y),
    Equation(
      plus(x, S(y)),
      S(plus(x,y))))

  val eqXPYP0EXPY = Equation(plus(plus(a,b),zero), plus(a,b))
  val eqYP0EY = Equation(plus(b,zero), b)

  val axXPYP0EXPY = Axiom(eqXPYP0EXPY)
  val axYP0EY = Axiom(eqYP0EY)

  val refXPY = Axiom(Nil, List(Equation(plus(a,b),plus(a,b))))

  val inductionBaseL =
    ForallLeftRule(
      axXPYP0EXPY,
      eqXPYP0EXPY,
      axAdd0,
      plus(a,b))
  
  val inductionBaseRL =
    ForallLeftRule(
      axYP0EY,
      eqYP0EY,
      axAdd0,
      b)

  val inductionBaseR =
    EquationRightRule(
      inductionBaseRL,
      refXPY,
      eqYP0EY,
      Equation(plus(a,b),plus(a,b)),
      Equation(
         plus(a,b),
         plus(a,plus(b,zero))
      )
    )

  val inductionBase =
  ContractionMacroRule(
    EquationRightRule(
      inductionBaseL,
      inductionBaseR,
      eqXPYP0EXPY,
      Equation(
        plus(a,b),
        plus(a,plus(b,zero))
      ),
      Equation(
        plus(plus(a,b), zero),
        plus(a,plus(b,zero))
      )
    )
  )

  val inductionStepDummy =
    Axiom(List(assocXYZ), List(assocXYSZ))

  val inductionProof =
  ForallRightBlock(
    InductionRule(
      inductionBase,
      inductionStepDummy,
      assocXY0,
      assocXYZ,
      assocXYSZ
    ),
    assoc,
    List(a,b,c)
  )

}
