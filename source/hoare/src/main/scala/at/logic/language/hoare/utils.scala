package at.logic.language.hoare

import at.logic.language.fol._

object usedVariables {
  def apply(p: Program): List[FOLVar] = p match {
    case Assign(x, t) => x :: freeVariables(t)
    case IfElse(c, a, b) => freeVariables(c) ++ usedVariables(a) ++ usedVariables(b)
    case ForLoop(i, n, b) => i :: n :: usedVariables(b)
    case Skip() => Nil
    case Sequence(a, b) => usedVariables(a) ++ usedVariables(b)
  }
}

object mapVariableNames {
  def apply(p: Program, f: String => String): Program =
    substVariables(p, (x: FOLVar) => FOLVar(f(x.name)))
}

object substVariables {
  def apply(p: Program, f: Map[FOLVar, FOLExpression]): Program =
    apply(p, (x: FOLVar) => f.getOrElse(x, x))

  def apply(p: Program, f: FOLVar => FOLExpression): Program = p match {
    case Assign(x, t) => Assign(f(x).asInstanceOf[FOLVar], apply(t, f))
    case IfElse(c, a, b) => IfElse(apply(c, f), apply(a, f), apply(b, f))
    case ForLoop(i, n, b) => ForLoop(f(i).asInstanceOf[FOLVar], f(n).asInstanceOf[FOLVar], apply(b, f))
    case Skip() => Skip()
    case Sequence(a, b) => Sequence(apply(a, f), apply(b, f))
  }

  def apply(t: FOLTerm, f: FOLVar => FOLExpression): FOLTerm = makeSubstitution(t, f)(t)
  def apply(t: FOLFormula, f: FOLVar => FOLExpression): FOLFormula = makeSubstitution(t, f)(t)

  private def makeSubstitution(t: FOLExpression, f: FOLVar => FOLExpression) =
    Substitution(freeVariables(t) map ((x: FOLVar) => x -> f(x)))
}

object LoopFree {
  def unapply(p: Program): Option[Program] = p match {
    case Assign(_, _) => Some(p)
    case IfElse(_, LoopFree(_), LoopFree(_)) => Some(p)
    case Skip() => Some(p)
    case Sequence(LoopFree(_), LoopFree(_)) => Some(p)
    case _ => None
  }
}

object weakestPrecondition {
  def apply(p: Program, f: FOLFormula): FOLFormula = p match {
    case Assign(x, t) => Substitution(x, t)(f)
    case IfElse(c, a, b) => And(Imp(c, weakestPrecondition(a, f)), Imp(Neg(c), weakestPrecondition(b, f)))
    case Skip() => f
    case Sequence(a, b) => weakestPrecondition(a, weakestPrecondition(b, f))
  }
}