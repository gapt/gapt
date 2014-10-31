package at.logic.language.hoare

import at.logic.calculi.lk.base.FSequent
import at.logic.language.fol._

object unrollLoop {
  def apply(p: Program, actualN: Int): Program = p match {
    case ForLoop(i, n, b) => Sequence(
        (0 until actualN).map(actualI =>
          substVariables(b, Map(i -> numeral(actualI), n -> numeral(actualN)))))
  }
}

object numeral {
  def apply(k: Int) = Utils.iterateTerm(FOLConst("o"), "s", k)
}

class SimpleLoopProblem(val loop: ForLoop, val gamma: Seq[FOLFormula], val precondition: FOLFormula, val postcondition: FOLFormula) {
  val programVariables = usedVariables(loop.body).distinct diff List(loop.indexVar, loop.limit)

  def stateFunctionSymbol(programVariable: FOLVar): String = programVariable match { case FOLVar(sym) => s"sigma_$sym" }

  def varsAtTime(i: Int): List[(FOLVar, FOLTerm)] =
    programVariables map { v => v -> Function(stateFunctionSymbol(v), List(numeral(i))) }

  def pi(i: Int): FOLFormula =
    Substitution(varsAtTime(i) :+ (loop.indexVar -> numeral(i)))(
      weakestPrecondition(loop.body,
        And(varsAtTime(i+1) map { case (v,s) => Equation(s, v) })))

  def instanceSequent(n: Int) = FSequent(gamma
      ++ ((0 until n) map pi map Substitution(loop.limit, numeral(n)).apply)
      :+ Substitution(varsAtTime(0) ++ List(loop.indexVar -> numeral(0), loop.limit -> numeral(n)))(precondition),
    List(Substitution(varsAtTime(n) ++ List(loop.indexVar -> numeral(n), loop.limit -> numeral(n)))(postcondition)))
}
