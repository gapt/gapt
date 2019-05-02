package gapt.formats.hoare

import gapt.expr._
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.proofs.hoare._
import gapt.formats.prover9.{ Prover9TermParserA, Prover9TermParserLadrStyle }

import scala.util.parsing.combinator.PackratParsers

trait ProgramParserA extends Prover9TermParserA {
  def program: PackratParser[Program] = singleStmt ~ rep( ";" ~> program ) ^^ {
    case p ~ ps => Sequence( p :: ps )
  }

  def singleStmt: PackratParser[Program] = skip | forLoop | ifElse | assign

  def assign: PackratParser[Assign] = variable ~ ":=" ~ term ^^ {
    case x ~ _ ~ ( t: FOLTerm ) => Assign( x, t )
  }

  def forLoop: PackratParser[ForLoop] = "for" ~ variable ~ "<" ~ variable ~ "do" ~ program ~ "od" ^^ {
    case _ ~ i ~ _ ~ n ~ _ ~ b ~ _ => ForLoop( i, n, b )
  }

  def ifElse: PackratParser[IfElse] = "if" ~ formula ~ "then" ~ program ~ "else" ~ program ~ "fi" ^^ {
    case _ ~ ( c: FOLFormula ) ~ _ ~ a ~ _ ~ b ~ _ => IfElse( c, a, b )
  }

  def skip: PackratParser[Skip] = "skip" ^^ { _ => Skip() }
}

object ProgramParser extends ProgramParserA {
  def parseProgram( input: String ): Program = parseAll( program, input ) match {
    case Success( p, _ ) => p
    case NoSuccess( msg, input ) =>
      throw new Exception( s"Error parsing program ${input.source} at ${input.pos}: $msg" )
  }

  override def conssymb: Parser[String] = """([a-tA-Z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] = """[u-z][a-zA-Z0-9_]*""".r
}
