/*
 * FOLResolutionCommandsParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.commandsParsers

import at.logic.provers.atp.commands._
import at.logic.unification.UnificationAlgorithm
import at.logic.language.lambda.substitutions._
import at.logic.calculi.resolution.base._

trait FOLResolutionCommandsParser extends CommandsParser {
  var unifAlg: UnificationAlgorithm = at.logic.unification.fol.FOLUnificationAlgorithm

  def parse(combinedCommand: Command, currentCommand: Command): Command = (combinedCommand, currentCommand) match {
    case (a, SetUnificationAlgorithmCom(alg)) => unifAlg = alg; a
    case (ApplyOnClausesCom((c1pre, c2pre)), ApplyOnAllLiteralPairsCom(commands)) => {
      val c1 = Variant(c1pre)
      val c2 = Variant(c2pre)
      AppendCommandsCom(
      ((for (i <- 0 to c1.root.negative.size - 1; j <- 0 to c2.root.positive.size - 1) yield (i,j + c2.root.negative.size)) ++
        (for (i <- 0 to c1.root.positive.size - 1; j <- 0 to c2.root.negative.size - 1) yield (i + c1.root.negative.size,j)))
          .flatMap(x => ApplyOnLiteralPositionCom(x, (c1, c2)) :: commands)
      )
    }
    // dummy for skipping the EmptyCom before applying to specific literals
    case (EmptyCom, a) => a
    case (ApplyOnLiteralPositionCom((i,j),(c1,c2)), ResolveCom) => {
      unifAlg.unify(c1.root(i), c2.root(j)) match {
        case None => NoResolventCom
        case Some(sub) => ResolventCom(Resolution(c1,c2,i,j,sub))
      }
    }
    case _ => Console.println(combinedCommand + " - " + currentCommand); FailureCom
  }
}
