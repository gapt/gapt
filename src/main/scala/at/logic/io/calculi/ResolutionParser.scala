/*
 * ResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.io.calculi
import at.logic.proofs.lk.base._
import at.logic.io.InputParser

trait ResolutionParser extends InputParser {
  def clauseList: Parser[List[FSequent]]
  def getClauseList(): List[FSequent] = {
    val reader = getInput()
    try {
      parseAll( clauseList, reader ).get
    } finally {
      reader.close();
    }
  }
}
