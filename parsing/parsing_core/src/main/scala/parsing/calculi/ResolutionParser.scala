/*
 * ResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi

import at.logic.calculi.resolution.base._

trait ResolutionParser extends InputParser {
    def clauseList : Parser[List[Clause]]
    def getClauseList(): List[Clause] = {
        val reader = getInput()
        try
        {
          parseAll(clauseList, reader).get
        }
        finally
        {
          reader.close();
        }
    }
}