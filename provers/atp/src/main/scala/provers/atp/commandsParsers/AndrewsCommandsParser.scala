/*
 * FOLResolutionCommandsParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.commandsParsers

import at.logic.provers.atp.commands._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.calculi.resolution.base._
import at.logic.calculi.resolution.robinson._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.replacements._

package andrews {
  
}

import andrews._

object AndrewsCommandsParser extends CommandsParser with at.logic.utils.logging.Logger {

  def parse(combinedCommand: Command, currentCommand: Command): Command = (combinedCommand, currentCommand) match {
    
    case _ => Console.println(combinedCommand + " - " + currentCommand); FailureReply // we can call here robinson in order to support also robinson resolution calculus
  }
}