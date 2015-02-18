/*
 * ResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.io.calculi
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.io.InputParser

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
