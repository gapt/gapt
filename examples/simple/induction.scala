import at.logic.gapt.language.fol._
import at.logic.gapt.proofs.lk._

object inductionExamples {

  val (x,y,z) = (FOLVar("x"), FOLVar("y"), FOLVar("z"))
  val (a,b,c) = (FOLVar("α"), FOLVar("β"), FOLVar("γ"))
  def S(x: FOLTerm) = FOLFunction("S", List(x))
  def plus(x: FOLTerm, y: FOLTerm) = FOLFunction("+", List(x,y))
  val zero = FOLConst("0")

  val assoc = AllVarBlock(List(x,y,z), FOLEquation(plus(plus(x,y),z), plus(x, plus(y,z)))).asInstanceOf[FOLFormula]
  val assocXYZ = FOLEquation(plus(plus(a,b),c), plus(a, plus(b,c)))
  val assocXY0 = FOLEquation(plus(plus(a,b), zero), plus(a, plus(b, zero)))
  val assocXYSZ = FOLEquation(plus(plus(a,b),S(c)), plus(a, plus(b,S(c))))

  def add0(v: FOLTerm) = FOLEquation(plus(v,zero), v)
  val axAdd0 = FOLAllVar(x, add0(x))

  def addS(u: FOLTerm, v: FOLTerm) =
  FOLEquation(
    plus(u, S(v)),
    S(plus(u,v))
  )
  val axAddS = AllVarBlock(List(x,y), addS(x,y))

  def ref(t: FOLTerm) = FOLEquation(t,t)

  val eqXPYP0EXPY = FOLEquation(plus(plus(a,b),zero), plus(a,b))
  val eqYP0EY = FOLEquation(plus(b,zero), b)

  val axXPYP0EXPY = Axiom(eqXPYP0EXPY)
  val axYP0EY = Axiom(eqYP0EY)

  val refXPY = Axiom(Nil, List(FOLEquation(plus(a,b),plus(a,b))))

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
  FOLEquation(plus(a,b), plus(a,plus(b,zero)))
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
