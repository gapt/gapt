package at.logic.parsing.hoare

import at.logic.language.fol.{FOLFormula, FOLTerm, FOLVar}
import at.logic.language.hoare._
import at.logic.parsing.language.prover9.{Prover9TermParserLadrStyle, Prover9TermParserA}
import scala.util.parsing.combinator.PackratParsers

trait ProgramParserA extends Prover9TermParserA {
  def program: PackratParser[Program] = singleStmt ~ rep(";" ~> program) ^^ {
    case p ~ ps => Sequence(p :: ps)
  }

  def singleStmt: PackratParser[Program] = skip | forLoop | ifElse | assign

  def assign: PackratParser[Assign] = variable ~ ":=" ~ term ^^ {
    case x ~ ":=" ~ (t: FOLTerm) => Assign(x, t)
  }

  def forLoop: PackratParser[ForLoop] = "for" ~ variable ~ "<" ~ variable ~ "do" ~ program ~ "od" ^^ {
    case "for" ~ i ~ "<" ~ n ~ "do" ~ b ~ "od" => ForLoop(i, n, b)
  }

  def ifElse: PackratParser[IfElse] = "if" ~ formula ~ "then" ~ program ~ "else" ~ program ~ "fi" ^^ {
    case "if" ~ (c: FOLFormula) ~ "then" ~ a ~ "else" ~ b ~ "fi" => IfElse(c, a, b)
  }

  def skip: PackratParser[Skip] = "skip" ^^ { _ => Skip()}
}

object ProgramParser extends ProgramParserA {
  def parseProgram(input: String): Program = parseAll(program, input) match {
    case Success(p, _) => p
    case NoSuccess(msg, input) =>
      throw new Exception(s"Error parsing program ${input.source} at ${input.pos}: $msg")
  }

  override def conssymb: Parser[String] = """([a-tA-Z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] =  """[u-z][a-zA-Z0-9_]*""".r
}
