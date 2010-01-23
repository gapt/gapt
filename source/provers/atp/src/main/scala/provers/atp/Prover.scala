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
/**
 * A generic prover for resolution calculus. Not thread safe!
 */
trait Prover {
  /**
   * Refutes input clauses if possible
   * @param clausesInput the input clauses
   * @return a stream that instantiate all possible refutations
   */
  def refute(commands: Stream[Command]) : Stream[ResolutionProof] = {
    // commands can be
    // get x clauses from refinemet
    // resolve on position x (later)
    // resolve on all positions
    // para modulate on all positions
    // factorize on clauses before given to resolution
    // check if tautology
    // check if subsumed by clauses in set
    // add clause to set

    // commands on prover level should be
    // give clauses to prover
    // getXClauses
    // insertClause
    // apply para modulation
    // prover should execute command by command
    refute(commands, EmptyCom)
  }

  private def refute(commands: Stream[Command], lastCommand: Command): Stream[ResolutionProof] =
    refuteOne(commands, lastCommand) match {
      case (None, _) => Stream.empty
      case (Some(p), (comms, compocom)) => Stream.cons(p, refute(comms, compocom))
    }

  /*
   * we want to combine the generation of one refutation within the stream so:
   * 1) once we have a refutation we return it immediately
   * 2) when asked for another we continue from the point we stopped
   * In order to achieve this refuteOne must return a refutation when one was found but also return
   * the current state of the commands (last command, stream of next commands)
   *
   * In case ResolventsFoundCom is obtained, a check must be made to see if it is the required one
   * if no, find a solution for iterating on all resolvents
   * if yes, return it and append to the remainingCommands stream a correct stream that will also take into
   * account the existence of some other resolvents that should be inserted into the refinement (maybe)
   *
   * An example set of commands: init clauses, repeat begin, get clauses, factorize, resolve, tautology deletion,
   * subsumed deletion, insert, end.
   */
  private def refuteOne(commands: Stream[Command], last: Command) : Tuple2[Option[ResolutionProof],Tuple2[Stream[Command],Command]] =
    refuteOne1Step(last, commands.head) match {
      case CorrectResolventFound(res) => (Some(res),(commands.tail,CorrectResolventFound(res)))
      case FailureCom => (None, (commands.tail, FailureCom))
      // if the command was to insert into command stream
      case AppendCommandsCom(coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), EmptyCom)
      case x => refuteOne(commands.tail, x)
    }

  /*
   * commands which affect several objects are divided into smaller steps
   */
  private def refuteOne1Step(composedCommand: Command, newCommand: Command): Command = (composedCommand, newCommand) match {
    // insert clauses to set
    case (EmptyCom, SetTargetResolventCom(tProof)) => targetProof = tProof; EmptyCom
    // deal with the case the input set already contains the target clause
    // therefore it returns the default empty clause as no refutation was made
    case (EmptyCom, InsertClausesCom(clauses)) if targetExistsIn(clauses) => CorrectResolventFound(targetProof)
    case (EmptyCom, InsertClausesCom(clauses)) => refinement.insertClauses(clauses); EmptyCom
    // try to obtain the required clauses, return fail command if not possible
    case (EmptyCom, GetClausesCom) => refinement.getClauses match {
      case None => FailureCom
      case Some(clauses) => ApplyOnClausesCom(clauses)
    }
    case (ResolventCom(res), InsertCom) if (targetProof.root.formulaEquivalece(res.root)) => CorrectResolventFound(res)
    case (ResolventCom(res), InsertCom) => refinement.insertProof(res); EmptyCom
    // pass parsing to customized commands parser
    case (NoResolventCom, InsertCom) => EmptyCom
    case _ => commandsParser.parse(composedCommand, newCommand)
  }

  private def targetExistsIn(clauses: List[Clause]) = clauses.exists(a => targetProof.root.formulaEquivalece(a))
  var targetProof: ResolutionProof = theEmptyClause() // override in commands if target is different
  // to be implemented in specific traits
  def refinement: Refinement
  def commandsParser: CommandsParser
}
