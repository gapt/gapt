/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol.propositions._
import at.logic.parsing.calculi.ResolutionParser
import refinements._
import commands._
import commandsParsers._
import ui.UserInterface

import java.util.Calendar

/**
 * A generic prover for resolution calculus. Not thread safe!
 */
object Prover {
    def main(args: Array[String]) {
      val prover = new Prover{}
      
      ()
    }
  }

trait Prover {
  /**
   * Refutes input clauses if possible
   * @param clausesInput the input clauses
   * @return a stream that instantiate all possible refutations
   */
  def refute(commands: Stream[Command]) : Stream[ResolutionProof] = {
    startingTime = (Calendar.getInstance().getTimeInMillis / 1000)
    // here we have the commands that are before the refutation process
    // such as loading the commands parser and refinement
    
    refute(commands, EmptyCom)
  }

  private def refute(commands: Stream[Command], lastCommand: Command): Stream[ResolutionProof] =
    refuteOne(commands, lastCommand) match {
      case (None, _) => Stream.empty
      case (Some(p), (comms, compocom)) => Stream.cons(p, refute(comms, compocom))
    }

  private def refuteOne(commands: Stream[Command], last: Command) : Tuple2[Option[ResolutionProof],Tuple2[Stream[Command],Command]] =
    refuteOne1Step(last, commands.head) match {
      case CorrectResolventFound(res) => (Some(res),(commands.tail,CorrectResolventFound(res)))
      case FailureCom => (None, (commands.tail, FailureCom))
      // if the command was to insert into command stream
      case AppendCommandsCom(coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), EmptyCom)
      case x => refuteOne(commands.tail, x)
    }

  private def refuteOne1Step(composedCommand: Command, newCommand: Command): Command = 
    if (timeLimit > 0 && (Calendar.getInstance().getTimeInMillis / 1000) - startingTime > timeLimit) FailureCom
    else
    (composedCommand, newCommand) match {
      case (EmptyCom, SetTimeLimit(n)) => timeLimit = n; EmptyCom
      case (EmptyCom, SetUICom(uinterface)) => userInterface = uinterface; EmptyCom
      case (EmptyCom, SetRefinementCom(ref)) => refinement = ref; EmptyCom
      case (EmptyCom, SetCommandsParserCom(comparse)) => commandsParser = comparse; EmptyCom
      case (EmptyCom, ErrorCom(msg)) if userInterface == null => FailureCom
      case (EmptyCom, ErrorCom(msg)) => userInterface.parse(ErrorCom(msg))
      // ensures that all settings were set
      case (EmptyCom, a) if (userInterface == null || refinement == null || commandsParser == null) =>
        AppendCommandsCom(ErrorCom("ui, refinement or commandsParser were not initialized")::a::Nil)
      // insert clauses to set
      case (EmptyCom, SetTargetResolventCom(tProof)) => targetProof = tProof; EmptyCom
      // deal with the case the input set already contains the target clause
      // therefore it returns the default empty clause as no refutation was made
      case (EmptyCom, InsertClausesCom(clauses)) if targetExistsIn(clauses) => CorrectResolventFound(targetProof)
      case (EmptyCom, InsertClausesCom(clauses)) => refinement.insertClauses(clauses); EmptyCom
      // try to obtain the required clauses, return fail command if not possible
      case (EmptyCom, GetClausesCom) => refinement.getClauses match {
        case None => FailureCom
        case Some(clauses) => GotClausesPairCom(clauses)
      }
      case (ResolventCom(res), InsertCom) if (targetProof.root.formulaEquivalece(res.root)) => CorrectResolventFound(res)
      case (ResolventCom(res), InsertCom) => refinement.insertProof(res); EmptyCom
      // pass parsing to customized commands parser
      case (NoResolventCom, InsertCom) => EmptyCom
      case _ => commandsParser.parse(composedCommand, newCommand)
    }

  private def targetExistsIn(clauses: List[Clause]) = clauses.exists(a => targetProof.root.formulaEquivalece(a))

  var targetProof: ResolutionProof = theEmptyClause() // override in commands if target is different
  var timeLimit: Long = -1
  var startingTime: Long = -1
  var refinement: Refinement = null
  var commandsParser: CommandsParser = null
  var userInterface: UserInterface = null
}
