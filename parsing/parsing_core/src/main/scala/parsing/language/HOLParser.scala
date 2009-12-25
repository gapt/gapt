/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language

import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._

trait HOLParser extends InputParser {
    def term : Parser[HOLTerm]
    def getTerm(): HOLTerm = {
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
