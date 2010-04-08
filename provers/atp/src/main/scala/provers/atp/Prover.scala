/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol._
import at.logic.parsing.calculi.ResolutionParser
import at.logic.algorithms.subsumption.{StillmanSubsumptionAlgorithm, SubsumptionAlgorithm} // to enable configuration
import refinements._
import commands._
import commandsParsers._
import ui._
import java.util.Calendar
import at.logic.utils.ds.PublishingBuffer
import at.logic.algorithms.subsumption.managers.SubsumptionManager

/**
 * A generic prover for resolution calculus. Not thread safe!
 */
object Main {
  def main(args: Array[String]) {
    val prover = new Prover[at.logic.calculi.resolution.robinson.Clause]{val panel = RobinsonCommandLinePanel}
    prover.recExec(Stream(InteractCom))
  }
}

trait Prover[V <: Sequent] extends at.logic.utils.logging.Logger {

  // for executing repeatedly (can be broken only with interactiveness (scala.actors.Actor.self.exit))
  def recExec(commands: Stream[Command]): Stream[ResolutionProof[V]] = {
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
  def refute(commands: Stream[Command]) : Stream[ResolutionProof[V]] = {
    startingTime = (Calendar.getInstance().getTimeInMillis / 1000)
    // here we have the commands that are before the refutation process
    // such as loading the commands parser and refinement
    
    refute(commands, EmptyCom)
  }

  private def refute(commands: Stream[Command], lastCommand: Command): Stream[ResolutionProof[V]] =
    refuteOne(commands, lastCommand) match {
      case (None, (_, ExitCom)) => scala.actors.Actor.self.exit
      case (None, _) => Stream.empty
      case (Some(p), (comms, compocom)) => Stream.cons(p, refute(comms, compocom))
    }

  private def refuteOne(commands: Stream[Command], last: Command) : Tuple2[Option[ResolutionProof[V]],Tuple2[Stream[Command],Command]] = if (commands.isEmpty) (None, (Stream.empty, FailureReply))
    else {
      //debug("ATP - 1 step -> last command: " + last + " --- current command: " + commands.head)
      refuteOne1Step(last, commands.head) match {
      case CorrectResolventFoundReply(res) => (Some(res.asInstanceOf[ResolutionProof[V]]),(commands.tail,CorrectResolventFoundReply(res)))
      case FailureReply => (None, (commands.tail, FailureReply))
      case ExitCom => (None, (commands.tail, ExitCom))
      // if the command was to insert into command stream
      // it can also be used in order to force the space (empty) command to be before
      case AppendCommandsCom(coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), EmptyCom)
      case AppendCommandsWithLastCom(lst, coms) => refuteOne(coms.foldRight(commands.tail)((a,b) => Stream.cons(a,b)), lst)
      case x => refuteOne(commands.tail, x)
      }
    }

  private def refuteOne1Step(composedCommand: Command, newCommand: Command): Command = 
    if (timeLimit > 0 && (Calendar.getInstance().getTimeInMillis / 1000) - startingTime > timeLimit) FailureReply
    else
    (composedCommand, newCommand) match {
      // interactiveness
      case (com, InteractCom) => {val c = panel.getNextCommand(com, if (pb != None) Some(pb.get.elements) else None); /*Console.println("interactive com: " + c);*/ c}
      case (EmptyCom, SetTimeLimit(n)) => timeLimit = n; EmptyCom
      case (EmptyCom, SetClausesCom(clauseList)) => pb = Some(new at.logic.utils.ds.PublishingBuffer[V]); pb.get.insertAll(0,clauseList.asInstanceOf[List[V]]); EmptyCom
      // ensures the clauses are loaded
      case (_, e @ ErrorReply(msg)) => AppendCommandsWithLastCom(e,InteractCom::Nil)
      case (_, a) if (pb == None) => AppendCommandsCom(ErrorReply("clauses were not loaded")::a::Nil)
      case (EmptyCom, SetRefinementCom(refCreator)) => refinement = Some(refCreator.asInstanceOf[PublishingBuffer[V] => Refinement[V]](pb.get)); EmptyCom
      case (EmptyCom, SetSubsumptionManagerCom(subsumCreator)) => subsumpMng = Some(subsumCreator.asInstanceOf[PublishingBuffer[V] => SubsumptionManager](pb.get)); EmptyCom
      case (EmptyCom, SetCommandsParserCom(comparse)) => commandsParser = Some(comparse); EmptyCom
      // ensures that all settings were set
      case (_, a) if (refinement == None || commandsParser == None) => AppendCommandsCom(ErrorReply("refinement or commandsParser were not initialized")::a::Nil)
      // insert clauses to set
      case (EmptyCom, SetTargetResolventCom(tProof)) => targetProof = tProof; EmptyCom
      // deal with the case the input set already contains the target clause
      // therefore it returns the default empty clause as no refutation was made
      case (EmptyCom, GetClausesCom) if targetExistsIn(refinement.get.clauses) => CorrectResolventFoundReply(targetProof)
      // try to obtain the required clauses, return fail command if not possible
      case (EmptyCom, ChooseClausesCom(c1,c2)) => refinement.get.getClausesPair(pb.get.apply(c1), pb.get.apply(c2)) match {
        case None => AppendCommandsCom(ErrorReply("Chosen clauses do not exist or were already resolved upon")::Nil)
        case Some(clauses) => GotClausesPairReply(clauses)
      }
      case (EmptyCom, GetClausesCom) => refinement.get.getNextClausesPair match {
        case None => FailureReply
        case Some(clauses) => GotClausesPairReply(clauses)
      }
      case (ResultedClauseReply(res), _) if (targetProof.root setEquals res.root) => CorrectResolventFoundReply(res)
      case (ResultedClauseReply(res), InsertCom) => {info(res.root.toString + " added"); refinement.get.insertProof(res.asInstanceOf[ResolutionProof[V]]); EmptyCom}
      case (r@ ResultedClauseReply(res), IfNotTautologyCom) => if (!res.root.antecedent.exists(f => res.root.succedent.contains(f))) r else {info(res.root.toString + " is a tautology"); NoResultedClauseReply()}
      case (r@ ResultedClauseReply(res), IfNotForwardSubsumedCom) => if (!subsumpMng.get.forwardSubsumption(res.root)) r else {info(res.root.toString + " is being subsumed"); NoResultedClauseReply()}
      case (r@ ResultedClauseReply(res), BackwardSubsumptionCom) => {subsumpMng.get.backwardSubsumption(res.root); r}
      case (NoResultedClauseReply(), InsertCom) => EmptyCom
      case (NoResultedClauseReply(), IfNotTautologyCom) => NoResultedClauseReply()
      case (NoResultedClauseReply(), IfNotForwardSubsumedCom) => NoResultedClauseReply()
      case (NoResultedClauseReply(), BackwardSubsumptionCom) => NoResultedClauseReply()
      // logical commands
      case (com, AndCom(ls1, ls2)) => AppendCommandsCom((com::ls1):::(com::ls2))
      case (EmptyCom, a) => a // skip empty commands
      // pass parsing to customized commands parser
      case _ => commandsParser.get.parse(composedCommand, newCommand)
    }

  private def targetExistsIn(clauses: Iterable[V]) = clauses.exists(a => targetProof.root setEquals a)

  var targetProof = theEmptyClause() // override in commands if target is different
  var timeLimit: Long = -1
  var startingTime: Long = -1
  var refinement: Option[Refinement[V]] = None
  var commandsParser: Option[CommandsParser] = None
  var pb: Option[PublishingBuffer[V]] = None
  var subsumpMng: Option[SubsumptionManager] = None
  val panel: UIPanel[V]
}
