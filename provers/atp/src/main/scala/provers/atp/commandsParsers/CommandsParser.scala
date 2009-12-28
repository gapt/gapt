/*
 * CommandsParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.commandsParsers

import at.logic.provers.atp.commands._

trait CommandsParser {
  /*
   * works like the fold operator as it receives every time a command which
   * is the result of the previous call of parse. It returns the command to be
   * parsed next.
   */
  def parse(combinedCommand: Command, currentCommand: Command): Command
}
