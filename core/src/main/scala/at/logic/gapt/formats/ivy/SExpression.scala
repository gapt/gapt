package at.logic.gapt.formats.lisp

import scala.io.Source
import scala.util.{ Success, Failure, Try }
import at.logic.gapt.formats.lisp
import scala.collection.immutable
import org.parboiled2._

/**
 * Lisp SExpression Datatypes and Parser
 * This is a basic LISP S-expression parser, without quote character, macros or other fancy stuff.
 * Atoms have a reduced namespace and need to be extended if necessary.
 *
 * Printing a Datastructure should output valid Lisp.
 */
sealed abstract class SExpression

case class LAtom( name: String ) extends SExpression {
  override def toString = name
}

case class LList( elements: SExpression* ) extends SExpression {
  def ::( head: SExpression ) = LList( head +: elements: _* )
  def ++( list2: LList ) = LList( elements ++ list2.elements: _* )

  override def toString = "(" + elements.mkString( " " ) + ")"
}
object LFun {
  def apply( head: String, args: SExpression* ): LList =
    LList( ( LAtom( head ) +: args ): _* )
  def unapplySeq( list: LList ): Option[( String, Seq[SExpression] )] = list match {
    case LList( LAtom( head ), args @ _* ) => Some( head, args )
    case _                                 => None
  }
}
object LFunOrAtom {
  def unapplySeq( expression: SExpression ): Option[( String, Seq[SExpression] )] = expression match {
    case LFun( name, args @ _* ) => Some( name, args )
    case LAtom( name )           => Some( name, Seq() )
    case _                       => None
  }
}

case class LCons( car: SExpression, cdr: SExpression ) extends SExpression {
  override def toString = "( " + car + " . " + cdr + ")"
}

object SExpressionParser {
  def apply( fn: String ): List[SExpression] = parseFile( fn )

  def parseFile( fn: String ): List[SExpression] =
    parseString( Source.fromFile( fn ).mkString )

  def parseString( s: String ): List[SExpression] = {
    val parser = new SExpressionParser( s )
    parser.File.run() match {
      case Failure( error: ParseError ) =>
        throw new IllegalArgumentException( parser.formatError( error ) )
      case Failure( exception ) => throw exception
      case Success( value )     => value.toList
    }
  }

  def tryParseString( s: String ): Try[List[SExpression]] =
    new SExpressionParser( s ).File.run().map { _.toList }

}

class SExpressionParser( val input: ParserInput ) extends Parser {

  def WhiteSpace = rule { zeroOrMore( anyOf( " \n\r\t\f" ) | ( ';' ~ zeroOrMore( noneOf( "\n" ) ) ) ) }

  def Str = rule { '"' ~ capture( zeroOrMore( noneOf( "\"" ) ) ) ~ '"' ~ WhiteSpace ~> lisp.LAtom }
  def Atom = rule { capture( oneOrMore( noneOf( "() \n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.LAtom }

  def SExpr: Rule1[lisp.SExpression] = rule { Str | Atom | Parens }

  def Parens = rule {
    '(' ~ WhiteSpace ~ optional( SExpr ~ (
      ( '.' ~ WhiteSpace ~ SExpr ~> LCons ) |
      ( zeroOrMore( SExpr ) ~> ( ( car: lisp.SExpression, cdr: Seq[lisp.SExpression] ) => LList( ( car +: cdr ): _* ) ) )
    ) ) ~ ')' ~ WhiteSpace ~> { _.getOrElse( LList() ) }
  }

  def File: Rule1[Seq[lisp.SExpression]] = rule { WhiteSpace ~ zeroOrMore( SExpr ) ~ EOI }
}
