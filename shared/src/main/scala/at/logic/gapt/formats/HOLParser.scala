/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats

import at.logic.gapt.expr._

trait HOLParser extends InputParser {
  def goal: Parser[LambdaExpression]

  def getTerm(): LambdaExpression = {
    val reader = getInput()
    try {
      parseAll( goal, reader ) match {
        case Success( expression, _ ) => expression
        case NoSuccess( msg, input ) =>
          throw new Exception( "Error parsing expression " + input.source + " at " + input.pos + ": " + msg )
      }
    } finally {
      reader.close();
    }
  }
}
