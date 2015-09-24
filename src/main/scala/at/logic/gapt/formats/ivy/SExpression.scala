package at.logic.gapt.formats.lisp

import scala.io.Source
import scala.util.Try
import at.logic.gapt.formats.lisp
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

case class LAtom( name: String ) extends SExpression {
  override def toString = name
}

case class LList( elements: List[SExpression] ) extends SExpression {
  def ::( head: SExpression ) = LList( head :: elements )
  def ++( list2: LList ) = LList( elements ++ list2.elements )

  override def toString = "(" + elements.mkString( " " ) + ")"
}

case class LCons( car: SExpression, cdr: SExpression ) extends SExpression {
  override def toString = "( " + car + " . " + cdr + ")"
}

/* Parser for SExpressions  */
object SExpressionParser {
  def apply( fn: String ): List[SExpression] = parseFile( fn )

  def parseFile( fn: String ): List[SExpression] =
    parseString( Source.fromFile( fn ).mkString )

  def parseString( s: String ): List[SExpression] =
    tryParseString( s ).get

  def tryParseString( s: String ): Try[List[SExpression]] =
    new SExpressionParser( s ).File.run().map { _.toList }

}

class SExpressionParser( val input: ParserInput ) extends Parser {

  def WhiteSpace = rule { zeroOrMore( anyOf( " \n\r\t\f" ) | ( ';' ~ zeroOrMore( noneOf( "\n" ) ) ) ) }

  def Nl = rule { anyOf( "Nn" ) ~ anyOf( "Ii" ) ~ anyOf( "Ll" ) ~ WhiteSpace ~ push( LList( Nil ) ) }
  def Str = rule { '"' ~ capture( zeroOrMore( noneOf( "\"" ) ) ) ~ '"' ~ WhiteSpace ~> lisp.LAtom }
  def Atom = rule { capture( oneOrMore( noneOf( "() \n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.LAtom }

  def SExpr: Rule1[lisp.SExpression] = rule { Nl | Str | Atom | Parens }

  def Parens = rule {
    '(' ~ WhiteSpace ~ optional( SExpr ~ (
      ( '.' ~ WhiteSpace ~ SExpr ~> LCons ) |
      ( zeroOrMore( SExpr ) ~> ( ( car: lisp.SExpression, cdr: Seq[lisp.SExpression] ) => LList( car :: cdr.toList ) ) )
    ) ) ~ ')' ~ WhiteSpace ~> { _.getOrElse( LList( Nil ) ) }
  }

  def File = rule { WhiteSpace ~ zeroOrMore( SExpr ) ~ EOI }
}
