package at.logic.gapt.formats.lisp

import at.logic.gapt.formats.{ InputFile, lisp }
import org.parboiled2._

import scala.util.{ Failure, Success, Try }

/**
 * Lisp SExpression Datatypes and Parser
 * This is a basic LISP S-expression parser, without quote character, macros or other fancy stuff.
 * Atoms have a reduced namespace and need to be extended if necessary.
 *
 * Printing a Datastructure should output valid Lisp.
 */
sealed abstract class SExpression

sealed abstract class LAtom extends SExpression

case class LKeyword( name: String ) extends LAtom {
  override def toString = s":$name"
}

case class LSymbol( name: String ) extends LAtom {
  override def toString = name
}

case class LList( elements: SExpression* ) extends SExpression {
  def ::( head: SExpression ) = LList( head +: elements: _* )
  def ++( list2: LList ) = LList( elements ++ list2.elements: _* )

  override def toString = "(" + elements.mkString( " " ) + ")"
}
object LFun {
  def apply( head: String, args: SExpression* ): LList =
    LList( ( LSymbol( head ) +: args ): _* )
  def unapplySeq( list: LList ): Option[( String, Seq[SExpression] )] = list match {
    case LList( LSymbol( head ), args @ _* ) => Some( head, args )
    case _                                   => None
  }
}
object LFunOrAtom {
  def unapplySeq( expression: SExpression ): Option[( String, Seq[SExpression] )] = expression match {
    case LFun( name, args @ _* ) => Some( name, args )
    case LSymbol( name )         => Some( name, Seq() )
    case _                       => None
  }
}

case class LCons( car: SExpression, cdr: SExpression ) extends SExpression {
  override def toString = "( " + car + " . " + cdr + ")"
}

object SExpressionParser {
  def apply( fn: InputFile ): List[SExpression] = {
    val parser = new SExpressionParser( fn.read )
    parser.File.run() match {
      case Failure( error: ParseError ) =>
        throw new IllegalArgumentException( parser.formatError( error ) )
      case Failure( exception ) => throw exception
      case Success( value )     => value.toList
    }
  }

  def tryParse( fn: InputFile ): Try[List[SExpression]] =
    new SExpressionParser( fn.read ).File.run().map { _.toList }

}

class SExpressionParser( val input: ParserInput ) extends Parser {

  def WhiteSpace = rule { zeroOrMore( anyOf( " \n\r\t\f" ) | ( ';' ~ zeroOrMore( noneOf( "\n" ) ) ) ) }

  def Str = rule { '"' ~ capture( zeroOrMore( noneOf( "\"" ) ) ) ~ '"' ~ WhiteSpace ~> lisp.LSymbol }
  def Symbol = rule { capture( noneOf( ":() |\n\r\t\f;\"" ) ~ zeroOrMore( noneOf( "() |\n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.LSymbol }

  def QuotedSymbolEscapeSequence: Rule0 = rule { '\\' ~ ( ch( '|' ) | '\\' ) }

  def QuotedSymbolBody: Rule1[String] = rule {
    zeroOrMore(
      capture( QuotedSymbolEscapeSequence ) ~> { _.substring( 1 ) } |
        capture( noneOf( "\\|" ) ) ) ~> { ( _: Seq[String] ).mkString( "" ) }
  }

  def QuotedSymbol = rule {
    '|' ~ QuotedSymbolBody ~ '|' ~ WhiteSpace ~> lisp.LSymbol
  }

  def Keyword = rule {
    ':' ~ capture( oneOrMore( noneOf( ":() |\n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.LKeyword
  }

  def SExpr: Rule1[lisp.SExpression] = rule {
    ( Str | QuotedSymbol | Symbol | Keyword | Parens )
  }

  def Parens = rule {
    '(' ~ WhiteSpace ~ optional( SExpr ~ (
      ( '.' ~ WhiteSpace ~ SExpr ~> LCons ) |
      ( zeroOrMore( SExpr ) ~> ( ( car: lisp.SExpression, cdr: Seq[lisp.SExpression] ) => LList( ( car +: cdr ): _* ) ) ) ) ) ~ ')' ~ WhiteSpace ~> { _.getOrElse( LList() ) }
  }

  def File: Rule1[Seq[lisp.SExpression]] = rule { WhiteSpace ~ zeroOrMore( SExpr ) ~ EOI }
}
