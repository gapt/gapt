/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language

import at.logic.language.hol._
import at.logic.parsing.InputParser

trait HOLParser extends InputParser {
    def term : Parser[HOLExpression]
    def getTerm(): HOLExpression = {
        val reader = getInput()
        try
        {
          parseAll(term, reader).get
        }
        finally
        {
          reader.close();
        }
    }
}
