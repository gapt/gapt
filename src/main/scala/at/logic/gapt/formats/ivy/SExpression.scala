package at.logic.gapt.formats.lisp

import java.io.FileReader
import util.parsing.input.{ NoPosition, Position, Reader, PagedSeqReader }
import util.parsing.combinator.Parsers
import util.parsing.combinator.RegexParsers
import at.logic.gapt.formats.lisp
import util.parsing.combinator.PackratParsers
import scala.collection.immutable.PagedSeq
import scala.collection.mutable
import scala.collection.immutable

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
object SExpressionParser extends SExpressionParser {
  def dumpreader[T]( r: Reader[T] ): String = dumpreader_( r ).mkString( " " )
  private def dumpreader_[T]( r: Reader[T] ): immutable.List[T] = {
    var reader = r
    if ( reader.atEnd ) Nil
    else reader.first :: dumpreader_( reader.rest )
  }

  def apply( fn: String ): immutable.List[SExpression] = parseFile( fn )

  def parseFile( fn: String ): immutable.List[SExpression] = {
    val r = new PagedSeqReader( new PagedSeq[Char]( new FileReader( fn ).read ) )
    parseAll( rep( sexpr ), r ) match {
      case Success( sexp, _ ) =>
        sexp
      case NoSuccess( msg, in ) =>
        println( dumpreader( in.rest ) )
        throw new Exception( "S-Expression Parser Failed: " + msg + " at " + in.pos + " with remaning input:" + dumpreader( in.rest ) )
    }
  }

  def parseString( s: String ): immutable.List[SExpression] = {
    parseAll( rep( sexpr ), s ) match {
      case Success( sexp, _ ) =>
        sexp
      case NoSuccess( msg, in ) =>
        throw new Exception( "S-Expression Parser Failed: " + msg + " at " + in.pos + " with remaning input: " + dumpreader( in.rest ) )
    }

  }

}

class SExpressionParser extends RegexParsers with PackratParsers {
  // This override takes care of comments
  override val whiteSpace = """(\s|;.*)+""".r

  lazy val nil = """(?i)\Qnil\E""".r ^^ { _ => lisp.List( Nil ) }
  lazy val quotedAtom = """"[^"]*"""".r ^^ lisp.Atom
  lazy val atom =
    """[a-zA-Z0-9=_+\-*/<>:.]*[a-zA-Z0-9=_+\-*/<>:]+[a-zA-Z0-9=_+\-*/<>:.]*""".r ^^ lisp.Atom

  lazy val cons = "(" ~ sexpr ~ "." ~ sexpr ~ ")" ^^ { case ( _ ~ l ~ _ ~ r ~ _ ) => lisp.Cons( l, r ) }
  lazy val list = "(" ~> rep( sexpr ) <~ ")" ^^ lisp.List

  lazy val sexpr: PackratParser[lisp.SExpression] = nil | quotedAtom | atom | cons | list

  def parse( in: String ) =
    parseAll( rep( sexpr ), in )

}

