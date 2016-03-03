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

import scala.util.matching.Regex
import scala.util.parsing.combinator._

trait TypeParsers extends JavaTokenParsers {
  def Type: Parser[Ty] = ( arrowType | iType | oType )
  def iType: Parser[Ty] = "i" ^^ { x => Ti }
  def oType: Parser[Ty] = "o" ^^ { x => To }
  def indexType: Parser[Ty] = "e" ^^ { x => Tindex }
  def arrowType: Parser[Ty] = "(" ~> Type ~ "->" ~ Type <~ ")" ^^ { case in ~ "->" ~ out => in -> out }
}
