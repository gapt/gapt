package at.logic.gapt.formats.lisp

import java.io.{ File, FileReader }
import scala.io.Source
import scala.util.Try
import util.parsing.input.{ NoPosition, Position, Reader, PagedSeqReader }
import util.parsing.combinator.Parsers
import util.parsing.combinator.RegexParsers
import at.logic.gapt.formats.lisp
import util.parsing.combinator.PackratParsers
import scala.collection.immutable.PagedSeq
import scala.collection.mutable
import scala.collection.immutable
import org.parboiled2._

/**
 * ** Lisp SExpression Datatypes and Parser
 * This is a basic LISP S-expression parser, without quote character, macros or other fancy stuff.
 * Atoms have a reduced namespace and need to be extended if necessary.
 *
 * Some remarks:
 * (1) regexp parsers eat whitespace and newlines
 * (2) recursive cases have to be put first
 */

/* Basic Lisp Datastructures: Atom, Cons and List 
 * Namespace collisions in scala.*.List
 * Printing a Datastructure should output valid Lisp.
 */
sealed class SExpression

case class Atom( name: String ) extends SExpression {
  override def toString = name
}

case class List( elements: immutable.List[SExpression] ) extends SExpression {
  def ::( head: SExpression ) = lisp.List( head :: elements )
  def ++( list2: lisp.List ) = lisp.List( elements ++ list2.elements )

  override def toString = "(" + elements.mkString( " " ) + ")"
  //def prepend(head : SExpression, list : lisp.List) = lisp.List(head::list.list)
}

case class Cons( car: SExpression, cdr: SExpression ) extends SExpression {
  override def toString = "( " + car + " . " + cdr + ")"
}

/* Parser for SExpressions  */
object SExpressionParser {
  def apply( fn: String ): immutable.List[SExpression] = parseFile( fn )

  def parseFile( fn: String ): immutable.List[SExpression] =
    parseString( Source.fromFile( fn ).mkString )

  def parseString( s: String ): immutable.List[SExpression] =
    tryParseString( s ).get

  def tryParseString( s: String ): Try[immutable.List[SExpression]] =
    new SExpressionParser( s ).File.run().map { _.toList }

}

class SExpressionParser( val input: ParserInput ) extends Parser {

  def WhiteSpace = rule { zeroOrMore( anyOf( " \n\r\t\f" ) | ( ';' ~ zeroOrMore( noneOf( "\n" ) ) ) ) }

  def Nl = rule { anyOf( "Nn" ) ~ anyOf( "Ii" ) ~ anyOf( "Ll" ) ~ WhiteSpace ~ push( lisp.List( Nil ) ) }
  def Str = rule { '"' ~ capture( zeroOrMore( noneOf( "\"" ) ) ) ~ '"' ~ WhiteSpace ~> lisp.Atom }
  def Atom = rule { capture( oneOrMore( noneOf( "() \n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.Atom }

  def SExpr: Rule1[lisp.SExpression] = rule { Nl | Str | Atom | Parens }

  def Parens = rule {
    '(' ~ WhiteSpace ~ optional( SExpr ~ (
      ( '.' ~ WhiteSpace ~ SExpr ~> lisp.Cons ) |
      ( zeroOrMore( SExpr ) ~> ( ( car: lisp.SExpression, cdr: Seq[lisp.SExpression] ) => lisp.List( car :: cdr.toList ) ) )
    ) ) ~ ')' ~ WhiteSpace ~> { _.getOrElse( lisp.List( Nil ) ) }
  }

  def File = rule { WhiteSpace ~ zeroOrMore( SExpr ) ~ EOI }
}
