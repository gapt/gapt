package gapt.formats.lisp

import gapt.formats.{ InputFile, lisp }
import gapt.utils.Doc
import org.parboiled2._

import scala.util.{ Failure, Success, Try }

/**
 * Lisp SExpression Datatypes and Parser
 * This is a basic LISP S-expression parser, without quote character, macros or other fancy stuff.
 * Atoms have a reduced namespace and need to be extended if necessary.
 *
 * Printing a Datastructure should output valid Lisp.
 */
sealed abstract class SExpression {
  def toDoc: Doc
  override def toString: String = toDoc.render( 80 )
}

sealed abstract class LAtom extends SExpression

case class LKeyword( name: String ) extends LAtom {
  def toDoc = Doc.text( s":$name" )
}

case class LSymbol( name: String ) extends LAtom {
  def toDoc = Doc.text {
    if ( name == "" ) {
      s"|$name|"
    } else if ( name.matches( ".*[\n\r\t\f \")(;:|\\\\].*" ) ) {
      "|" + name.replace( "\\", "\\\\" ).replace( "|", "\\|" ) + "|"
    } else {
      name
    }
  }
}

case class LList( elements: SExpression* ) extends SExpression {
  def ::( head: SExpression ) = LList( head +: elements: _* )
  def ++( list2: LList ) = LList( elements ++ list2.elements: _* )

  def toDoc =
    ( Doc.text( "(" ) <> Doc.wordwrap2( elements.map( _.toDoc ), "" ) <> ")" ).
      nest( 2 ).group
}
object LList {
  def apply( elements: Iterable[SExpression] ): LList =
    LList( elements.toSeq: _* )
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
  def toDoc = ( Doc.text( "(" ) <> car.toDoc <+> "." </> cdr.toDoc <> ")" ).nest( 2 ).group
}

object SExpressionParser {
  def parse( fn: InputFile ): List[SExpression] = {
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

  private class SExpressionParser( val input: ParserInput ) extends Parser {

    private def WhiteSpace = rule { zeroOrMore( anyOf( " \n\r\t\f" ) | ( ';' ~ zeroOrMore( noneOf( "\n" ) ) ) ) }

    private def Str = rule { '"' ~ capture( zeroOrMore( noneOf( "\"" ) ) ) ~ '"' ~ WhiteSpace ~> lisp.LSymbol }
    private def Symbol = rule { capture( noneOf( ":() |\n\r\t\f;\"" ) ~ zeroOrMore( noneOf( "() |\n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.LSymbol }

    private def QuotedSymbolEscapeSequence: Rule0 = rule { '\\' ~ ( ch( '|' ) | '\\' ) }

    private def QuotedSymbolBody: Rule1[String] = rule {
      zeroOrMore(
        capture( QuotedSymbolEscapeSequence ) ~> { _.substring( 1 ) } |
          capture( noneOf( "\\|" ) ) ) ~> { ( _: Seq[String] ).mkString( "" ) }
    }

    private def QuotedSymbol = rule {
      '|' ~ QuotedSymbolBody ~ '|' ~ WhiteSpace ~> lisp.LSymbol
    }

    private def Keyword = rule {
      ':' ~ capture( oneOrMore( noneOf( ":() |\n\r\t\f;\"" ) ) ) ~ WhiteSpace ~> lisp.LKeyword
    }

    private def SExpr: Rule1[lisp.SExpression] = rule {
      ( Str | QuotedSymbol | Symbol | Keyword | Parens )
    }

    private def Parens = rule {
      '(' ~ WhiteSpace ~ optional( SExpr ~ (
        ( '.' ~ WhiteSpace ~ SExpr ~> LCons ) |
        ( zeroOrMore( SExpr ) ~> ( ( car: lisp.SExpression, cdr: Seq[lisp.SExpression] ) => LList( ( car +: cdr ): _* ) ) ) ) ) ~ ')' ~ WhiteSpace ~> { _.getOrElse( LList() ) }
    }

    def File: Rule1[Seq[lisp.SExpression]] = rule { WhiteSpace ~ zeroOrMore( SExpr ) ~ EOI }
  }

}

