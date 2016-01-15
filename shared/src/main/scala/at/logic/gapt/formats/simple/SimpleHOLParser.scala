/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.simple

import at.logic.gapt.expr.schema.Tindex
import at.logic.gapt.expr.{ To, FunctionType }
import at.logic.gapt.formats.HOLParser
import at.logic.gapt.expr._
import at.logic.gapt.formats.readers.StringReader

import scala.util.matching.Regex
import scala.util.parsing.combinator._

trait TypeParsers extends JavaTokenParsers {
  def Type: Parser[Ty] = ( arrowType | iType | oType )
  def iType: Parser[Ty] = "i" ^^ { x => Ti }
  def oType: Parser[Ty] = "o" ^^ { x => To }
  def indexType: Parser[Ty] = "e" ^^ { x => Tindex }
  def arrowType: Parser[Ty] = "(" ~> Type ~ "->" ~ Type <~ ")" ^^ { case in ~ "->" ~ out => in -> out }
}

trait SimpleHOLParser extends HOLParser with JavaTokenParsers with TypeParsers {
  def goal = term

  def term: Parser[LambdaExpression] = ( non_formula | formula )
  def formula: Parser[HOLFormula] = ( neg | atom | and | or | imp | forall | exists | variable | constant ) ^? {
    case trm: HOLFormula => trm.asInstanceOf[HOLFormula]
  }
  def non_formula: Parser[LambdaExpression] = ( abs | variable | constant | var_func | const_func )
  def variable: Parser[Var] = regex( new Regex( "[u-z]" + word ) ) ~ ":" ~ Type ^^ { case x ~ ":" ~ tp => Var( x, tp ) }
  def constant: Parser[Const] = regex( new Regex( "[a-tA-Z0-9]" + word ) ) ~ ":" ~ Type ^^ { case x ~ ":" ~ tp => Const( x, tp ) }
  def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ { case "And" ~ x ~ y => And( x, y ) }
  def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ { case "Or" ~ x ~ y => Or( x, y ) }
  def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ { case "Imp" ~ x ~ y => Imp( x, y ) }
  def abs: Parser[LambdaExpression] = "Abs" ~ variable ~ term ^^ { case "Abs" ~ v ~ x => Abs( v, x ) }
  def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ { case "Neg" ~ x => Neg( x ) }
  def atom: Parser[HOLFormula] = ( equality | var_atom | const_atom )
  def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ { case "Forall" ~ v ~ x => All( v, x ) }
  def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ { case "Exists" ~ v ~ x => Ex( v, x ) }
  def var_atom: Parser[HOLFormula] = regex( new Regex( "[u-z]" + word ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => HOLAtom( Var( x, FunctionType( To, params.map( _.exptype ) ) ), params )
  }
  def const_atom: Parser[HOLFormula] = regex( new Regex( "[" + symbols + "a-tA-Z0-9]" + word ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => HOLAtom( Const( x, FunctionType( To, params.map( _.exptype ) ) ), params )
  }
  def equality: Parser[HOLFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
  //def eq_infix: Parser[Formula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
  def eq_prefix: Parser[HOLFormula] = "=" ~ "(" ~ term ~ "," ~ term ~ ")" ^^ { case "=" ~ "(" ~ x ~ "," ~ y ~ ")" => Eq( x, y ) }
  def var_func: Parser[LambdaExpression] = regex( new Regex( "[u-z]" + word ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ~ ":" ~ Type ^^ {
    case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => HOLFunction( Var( x, FunctionType( tp, ( params.map( _.exptype ) ) ) ), params )
  }

  def const_func: Parser[LambdaExpression] = regex( new Regex( "[" + symbols + "a-tA-Z0-9]" + word ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ~ ":" ~ Type ^^ {
    case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => HOLFunction( Const( x, FunctionType( tp, ( params.map( _.exptype ) ) ) ), params )
  }

  protected def symbol: Parser[String] = symbols.r
  def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';
  protected val word: String = """[a-zA-Z0-9$_{}]*"""

}

object SimpleHOLParser {
  private class StringHOLParser( input: String ) extends StringReader( input ) with SimpleHOLParser

  def apply( s: String ) = new StringHOLParser( s ).getTerm
}
