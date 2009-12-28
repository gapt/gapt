/*
 * FOLResolutionCommandsParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.commandsParsers

import at.logic.provers.atp.commands._

trait FOLResolutionCommandsParser extends CommandsParser {
  def parse(combinedCommand: Command, currentCommand: Command): Command = (combinedCommand, currentCommand) match {
    case _ => FailureCom
  }
}
