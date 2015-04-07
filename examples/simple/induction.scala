import at.logic.calculi.lk._
import at.logic.gapt.proofs.lk.InductionRule
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

  def add0(v: FOLTerm) = Equation(plus(v,zero), v)
  val axAdd0 = AllVar(x, add0(x))

  def addS(u: FOLTerm, v: FOLTerm) =
  Equation(
    plus(u, S(v)),
    S(plus(u,v))
  )
  val axAddS = AllVarBlock(List(x,y), addS(x,y))

  def ref(t: FOLTerm) = Equation(t,t)

  val eqXPYP0EXPY = Equation(plus(plus(a,b),zero), plus(a,b))
  val eqYP0EY = Equation(plus(b,zero), b)

  val axXPYP0EXPY = Axiom(eqXPYP0EXPY)
  val axYP0EY = Axiom(eqYP0EY)

  val refXPY = Axiom(Nil, List(Equation(plus(a,b),plus(a,b))))

  val inductionBase1 =
  Axiom(
    List(add0(b), add0(plus(a,b))),
    List(ref(plus(a,b)))
  )

  val inductionBase2 =
  UnaryEquationRightRule(
  inductionBase1,
  inductionBase1.root.antecedent.head,
  inductionBase1.root.succedent.head,
  Equation(plus(a,b), plus(a,plus(b,zero)))
  )

  val inductionBase3 =
  UnaryEquationRightRule(
    inductionBase2,
    inductionBase2.root.antecedent.tail.head,
    inductionBase2.root.succedent.head,
    assocXY0
  )

  val inductionBase4 =
  ForallLeftRule(
    inductionBase3,
    inductionBase3.root.antecedent.tail.head,
    axAdd0,
    plus(a,b)
  )

  val inductionBase =
  ContractionMacroRule(
  ForallLeftRule(
    inductionBase4,
    inductionBase4.root.antecedent.head,
    axAdd0,
    b
  )
  )

  val inductionStepDummy =
    Axiom(List(assocXYZ), List(assocXYSZ))

  /*val inductionProof =
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
*/
  val inductionProof =
    ForallRightBlock(
      InductionRule(
        inductionBase,
        inductionStepDummy,
        assocXYZ
      ),
      assoc,
      List(a,b,c)
    )

}
