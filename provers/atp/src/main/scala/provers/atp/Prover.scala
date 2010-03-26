/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol._
import at.logic.parsing.calculi.ResolutionParser
import at.logic.algorithms.subsumption.{StillmanSubsumptionAlgorithm, SubsumptionAlgorithm} // to enable configuration
import refinements._
import commands._
import commandsParsers._
import ui.CommandLinePanel

import java.util.Calendar

/**
 * A generic prover for resolution calculus. Not thread safe!
 */
object Main {
  def main(args: Array[String]) {
    val prover = new Prover{val panel = CommandLinePanel}
    prover.recExec(Stream(InteractCom))
  }
}

trait Prover {

  // for executing repeatedly (can be broken only with interactiveness)
  def recExec(commands: Stream[Command]): Stream[ResolutionProof] = {
    refute(commands) match {
      case Stream.empty => recExec(Stream(NoResolventFoundReply, InteractCom))
      case a => val hd = a.head; recExec(Stream(ResolventFoundReply(hd), InteractCom))
    }
  }

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
      case (None, (_, ExitCom)) => scala.actors.Actor.self.exit
      case (None, _) => Stream.empty
      case (Some(p), (comms, compocom)) => Stream.cons(p, refute(comms, compocom))
    }

  private def refuteOne(commands: Stream[Command], last: Command) : Tuple2[Option[ResolutionProof],Tuple2[Stream[Command],Command]] = if (commands.isEmpty) (None, (Stream.empty, FailureCom))
    else {
      //Console.println("last command: " + last + " --- command: " + commands.head)
      refuteOne1Step(last, commands.head) match {
      case CorrectResolventFoundCom(res) => (Some(res),(commands.tail,CorrectResolventFoundCom(res)))
      case FailureCom => (None, (commands.tail, FailureCom))
      case ExitCom => (None, (commands.tail, ExitCom))
      // if the command was to insert into command stream
      // it can also be used in order to force the space (empty) command to be before
      case AppendCommandsCom(coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), EmptyCom)
      case AppendCommandsWithLastCom(lst, coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), lst)
      case x => refuteOne(commands.tail, x)
      }
    }

  private def refuteOne1Step(composedCommand: Command, newCommand: Command): Command = 
    if (timeLimit > 0 && (Calendar.getInstance().getTimeInMillis / 1000) - startingTime > timeLimit) FailureCom
    else
    (composedCommand, newCommand) match {
      // interactiveness
      case (com, InteractCom) => {val c = panel.getNextCommand(com, if (pb != None) Some(pb.get.elements) else None); /*Console.println("interactive com: " + c);*/ c}
      case (EmptyCom, SetTimeLimit(n)) => timeLimit = n; EmptyCom
      case (EmptyCom, SetClausesCom(clauseList)) => pb = Some(new at.logic.utils.ds.PublishingBuffer[Clause]); pb.get.insertAll(0,clauseList); EmptyCom
      // ensures the clauses are loaded
      case (_, e @ ErrorCom(msg)) => AppendCommandsWithLastCom(e,InteractCom::Nil)
      case (_, a) if (pb == None) => AppendCommandsCom(ErrorCom("clauses were not loaded")::a::Nil)
      case (EmptyCom, SetRefinementCom(refCreator)) => refinement = Some(refCreator(pb.get)); EmptyCom
      case (EmptyCom, SetSubsumptionManagerCom(subsumCreator)) => subsumpMng = Some(subsumCreator(pb.get)); EmptyCom
      case (EmptyCom, SetCommandsParserCom(comparse)) => commandsParser = Some(comparse); EmptyCom
      // ensures that all settings were set
      case (_, a) if (refinement == None || commandsParser == None) => AppendCommandsCom(ErrorCom("refinement or commandsParser were not initialized")::a::Nil)
      // insert clauses to set
      case (EmptyCom, SetTargetResolventCom(tProof)) => targetProof = tProof; EmptyCom
      // deal with the case the input set already contains the target clause
      // therefore it returns the default empty clause as no refutation was made
      case (EmptyCom, GetClausesCom) if targetExistsIn(refinement.get.clauses) => CorrectResolventFoundCom(targetProof)
      // try to obtain the required clauses, return fail command if not possible
      case (EmptyCom, ChooseClausesCom(c1,c2)) => refinement.get.getClausesPair(pb.get.apply(c1), pb.get.apply(c2)) match {
        case None => AppendCommandsCom(ErrorCom("Chosen clauses do not exist or were already resolved upon")::Nil)
        case Some(clauses) => GotClausesPairCom(clauses)
      }
      case (EmptyCom, GetClausesCom) => refinement.get.getNextClausesPair match {
        case None => FailureCom
        case Some(clauses) => GotClausesPairCom(clauses)
      }
      case (ResultedClauseCom(res), _) if (targetProof.root.formulaEquivalece(res.root)) => CorrectResolventFoundCom(res)
      case (ResultedClauseCom(res), InsertCom) => refinement.get.insertProof(res); EmptyCom
      case (r@ ResultedClauseCom(res), IfNotTautologyCom) => if (!res.root.negative.exists(f => res.root.positive.contains(f))) r else NoResultedClauseCom()
      case (r@ ResultedClauseCom(res), IfNotForwardSubsumedCom) => if (!subsumpMng.get.forwardSubsumption(res.root)) r else NoResultedClauseCom()
      case (r@ ResultedClauseCom(res), BackwardSubsumptionCom) => {subsumpMng.get.backwardSubsumption(res.root); r}
      case (NoResultedClauseCom(), InsertCom) => EmptyCom
      case (NoResultedClauseCom(), IfNotTautologyCom) => NoResultedClauseCom()
      case (NoResultedClauseCom(), IfNotForwardSubsumedCom) => NoResultedClauseCom()
      case (NoResultedClauseCom(), BackwardSubsumptionCom) => NoResultedClauseCom()
      // logical commands
      case (com, AndCom(ls1, ls2)) => AppendCommandsCom((com::ls1):::(com::ls2))
      case (EmptyCom, a) => a // skip empty commands
      // pass parsing to customized commands parser
      case _ => commandsParser.get.parse(composedCommand, newCommand)
    }

  private def targetExistsIn(clauses: Iterable[Clause]) = clauses.exists(a => targetProof.root.formulaEquivalece(a))

  var targetProof: ResolutionProof = theEmptyClause() // override in commands if target is different
  var timeLimit: Long = -1
  var startingTime: Long = -1
  var refinement: Option[Refinement] = None
  var commandsParser: Option[CommandsParser] = None
  var pb: Option[at.logic.utils.ds.PublishingBuffer[Clause]] = None
  var subsumpMng: Option[at.logic.algorithms.subsumption.managers.SubsumptionManager] = None
  val panel: {def getNextCommand(com:Command, elements: Option[Iterator[Clause]]): Command}
}
