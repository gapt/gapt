package at.logic.language.hoare

import at.logic.language.fol.{FOLFormula, FOLTerm, FOLVar}

abstract class Program {
  override def toString = this match {
    case Assign(v, t) => s"$v := $t"
    case IfElse(c, i, e) => s"if $c then $i else $e fi"
    case ForLoop(i, n, b) => s"for $i < $n do $b od"
    case Sequence(a, b) => s"$a; $b"
    case Skip() => "skip"
  }
}

case class Assign(val variable: FOLVar, val term: FOLTerm) extends Program
case class IfElse(val condition: FOLFormula, val ifBranch: Program, val elseBranch: Program) extends Program
case class ForLoop(val indexVar: FOLVar, val limit: FOLVar, val body: Program) extends Program
case class Sequence(val a: Program, val b: Program) extends Program
case class Skip() extends Program

object Assign {
  def apply(v: String, t: FOLTerm): Assign = Assign(FOLVar(v), t)
}

object ForLoop {
  def apply(i: String, n: String, b: Program): ForLoop = ForLoop(FOLVar(i), FOLVar(n), b)
}

object Sequence {
  def apply(programs: Seq[Program]): Program = apply(programs.to[List])

  def apply(programs: List[Program]): Program = programs match {
    case p :: ps => ps.foldLeft(p)(Sequence(_, _))
    case Nil => Skip()
  }
}

object Blocks {
  def unapply(program: Program): List[Program] = program match {
    case Sequence(a,b) => unapply(a) ++ unapply(b)
    case Skip() => Nil
    case _ => List(program)
  }
}