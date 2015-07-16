/*
 * ResolutionParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.simple

import at.logic.gapt.formats.InputParser
import at.logic.gapt.proofs.lk.base._

trait ResolutionParser extends InputParser {
  def clauseList: Parser[List[HOLSequent]]
  def getClauseList(): List[HOLSequent] = {
    val reader = getInput()
    try {
      parseAll( clauseList, reader ).get
    } finally {
      reader.close();
    }
  }
}
