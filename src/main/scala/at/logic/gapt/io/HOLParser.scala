/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.io

import at.logic.gapt.language.hol._

trait HOLParser extends InputParser {
  def goal: Parser[HOLExpression]

  def getTerm(): HOLExpression = {
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
