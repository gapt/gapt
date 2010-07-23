/*
 * ResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi

import at.logic.calculi.lk.base._
import at.logic.parsing.InputParser

trait ResolutionParser[V <: Sequent] extends InputParser {
    def clauseList : Parser[List[V]]
    def getClauseList(): List[V] = {
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
