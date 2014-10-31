package at.logic.parsing.hoare

import java.io.Reader

import at.logic.language.fol.{FOLFormula, FOLTerm, FOLVar}
import at.logic.language.hoare._
import at.logic.parsing.language.simple.SimpleFOLParser

trait ProgramParser extends SimpleFOLParser {
  override def variable: Parser[  FOLVar] = super.variable ^^ { case v: FOLVar => v }

  def program: Parser[Program] = singleStmt ~ rep(";" ~> program) ^^ {
    case p ~ ps => Sequence(p :: ps)
  }

  def singleStmt: Parser[Program] = skip | forLoop | ifElse | assign

  def assign: Parser[Assign] = variable ~ ":=" ~ non_formula ^^ {
    case x ~ ":=" ~ (t: FOLTerm) => Assign(x, t)
  }

  def forLoop: Parser[ForLoop] = "for" ~ variable ~ "<" ~ variable ~ "do" ~ program ~ "od" ^^ {
    case "for" ~ i ~ "<" ~ n ~ "do" ~ b ~ "od" => ForLoop(i, n, b)
  }

  def ifElse: Parser[IfElse] = "if" ~ formula ~ "then" ~ program ~ "else" ~ program ~ "fi" ^^ {
    case "if" ~ (c: FOLFormula) ~ "then" ~ a ~ "else" ~ b ~ "fi" => IfElse(c, a, b)
  }

  def skip: Parser[Skip] = "skip" ^^ { _ => Skip() }
}

object SimpleProgramParser extends ProgramParser {
  def parseProgram(input: String): Program = parseAll(program, input) match {
    case Success(p, _) => p
    case NoSuccess(msg, input) =>
      throw new Exception(s"Error parsing program ${input.source} at ${input.pos}: $msg")
  }

  override def getInput(): Reader = throw new NotImplementedError()
}