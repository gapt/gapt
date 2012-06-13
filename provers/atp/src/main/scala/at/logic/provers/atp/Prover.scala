/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import Definitions.State
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.calculi.resolution.robinson.Clause
import at.logic.language.fol.FOLExpression
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.FileReader
import at.logic.provers.atp.commands.base.BranchCommand
import at.logic.provers.atp.commands.base.Command
import at.logic.provers.atp.commands.base.DataCommand
import at.logic.provers.atp.commands.base.InitialCommand
import at.logic.provers.atp.commands.base.PrependCommand
import at.logic.provers.atp.commands.base.PrependOnCondCommand
import at.logic.provers.atp.commands.base.RestoreCommand
import at.logic.provers.atp.commands.base.ResultCommand
import at.logic.provers.atp.commands.base.SetStreamCommand
import at.logic.provers.atp.commands.base.SpawnCommand
import at.logic.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.provers.atp.commands.logical.DeterministicMacroCommand
import at.logic.utils.executionModels.ndStream.Configuration
import at.logic.utils.executionModels.ndStream.NDStream
import at.logic.utils.executionModels.searchAlgorithms.BFSAlgorithm
import commands.base.Command
import commands.robinson.FactorCommand
import commands.robinson.ParamodulationCommand
import commands.robinson.ResolveCommand
import commands.robinson.SetClausesCommand
import commands.robinson.VariantsCommand
import commands.sequents.ApplyOnAllPolarizedLiteralPairsCommand
import commands.sequents.InsertResolventCommand
import commands.sequents.RefutationReachedCommand
import commands.sequents.SearchForEmptyClauseCommand
import commands.sequents.SetTargetClause
import commands.sequents.SimpleBackwardSubsumptionCommand
import commands.sequents.SimpleForwardSubsumptionCommand
import commands.ui.PromptTerminal
import commands.ui.getTwoClausesFromUICommand
import scala.collection.mutable.HashMap

object Definitions {
  type State = HashMap[String, Any]
}

object Main {
  import commands.base._
  import commands.ui._
  import commands.sequents._
  import commands.robinson._
  import _root_.at.logic.provers.atp.commands.logical.DeterministicAndCommand
  import at.logic.calculi.resolution.robinson.Clause
  import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
  import at.logic.calculi.resolution.robinson.Clause
  import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
  import at.logic.language.fol.FOLExpression
  import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
  import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
  import at.logic.parsing.readers.FileReader

  def stream1:  Stream[Command[Clause]] = Stream.cons(getTwoClausesFromUICommand[Clause](PromptTerminal.GetTwoClauses),
    Stream.cons(VariantsCommand,
    Stream.cons(DeterministicAndCommand[Clause]((
      List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
      List(ParamodulationCommand(FOLUnificationAlgorithm)))),
    Stream.cons(SimpleForwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
    Stream.cons(SimpleBackwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
    Stream.cons(InsertResolventCommand[Clause],
    Stream.cons(RefutationReachedCommand[Clause], stream1)))))))
  def stream: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1))
  def main(args: Array[String]) {
    val prover = new Prover[at.logic.calculi.resolution.robinson.Clause]{}
    prover.refute(Stream.cons(SetClausesCommand((new FileReader(args(0)) with SimpleResolutionParserFOL).getClauseList), stream)).next
  }
}

class ProverException(msg: String) extends Exception(msg)

trait Prover[V <: Sequent] extends at.logic.utils.logging.Logger {
  
  def refute(commands: Stream[Command[V]]) : NDStream[ResolutionProof[V]] = {
    new NDStream(new MyConfiguration(new State(), commands, ()), myFun) with BFSAlgorithm
  }
  
  private[Prover] class MyConfiguration(val state: State, val commands: Stream[Command[V]], val data: Any, val result: Option[ResolutionProof[V]]) extends Configuration[ResolutionProof[V]] {
    def this(state: State, commands: Stream[Command[V]], data: Any) = this(state, commands, data, None)
    def isTerminal = result != None
  }

  private[Prover] def myFun(c: Configuration[ResolutionProof[V]]): Iterable[Configuration[ResolutionProof[V]]] = {
    val conf = c.asInstanceOf[MyConfiguration]
    //Console.println("debug -- command: " + conf.commands.head.getClass + ", data: " + conf.data + ", next Command: " + conf.commands.tail.head.getClass)
    if (conf.commands.isEmpty) List()
    else {
      //if (!conf.commands.head.toString.matches("(VariantsCommand|IsGuidedNotFoundCommand|SimpleRefinementGetCommand|ClauseFactorCommand).*"))
      //    println("Prover Executing command: "+conf.commands.head.getClass+" :: "+conf.commands.head.toString)

      conf.commands.head match {
        case com: InitialCommand[_] => com(conf.state).map(x => new MyConfiguration(x._1, conf.commands.tail, x._2))
        case com: DataCommand[_] => {
          val res = com(conf.state, conf.data)
          if (res.isEmpty) List(new MyConfiguration(conf.state, skipNonInit(conf.commands.tail), ()))
          else res.map(x => new MyConfiguration(x._1, conf.commands.tail, x._2))
        }
        case com: ResultCommand[_] => List(new MyConfiguration(conf.state, conf.commands.tail, conf.data, com(conf.state, conf.data)))
        case com: DeterministicMacroCommand[_] => {
          val res = com(conf.state)
          res._1.map(x => new MyConfiguration(x._1, conf.commands.tail, conf.data, x._2)) ++
          (if (res._2) List(new MyConfiguration(conf.state, conf.commands.tail, conf.data)) else List())
        }
        case com: BranchCommand[_] => com.commands.map(x => new MyConfiguration(conf.state, x ++ conf.commands.tail, conf.data))
        case com: PrependCommand[_] => List(new MyConfiguration(conf.state, (com.commands).foldRight(conf.commands.tail)((x,c) => x +: c), conf.data))
        case com: PrependOnCondCommand[_] => if (com.cond(conf.state, conf.data)) List(new MyConfiguration(conf.state, (com.commands).foldRight(conf.commands.tail)((x,c) => x +: c), conf.data))
          else List(new MyConfiguration(conf.state, conf.commands.tail, conf.data))
        // this command should create a whole new subtree using different state and commands for replay of sub proofs
        case com: SpawnCommand[_] =>  {
          val state = new State() ++= conf.state += (("old_commands", conf.commands.tail)) += (("old_state", conf.state))
          List(new MyConfiguration(state, conf.data.asInstanceOf[Stream[Command[V]]],conf.data))
        }
        case com: RestoreCommand[_] => List(new MyConfiguration(conf.state("old_state").asInstanceOf[State], (com.commands).foldRight(conf.state("old_commands").asInstanceOf[Stream[Command[V]]])((x,c) => x +: c), conf.data))
        case com: SetStreamCommand[_] => List(new MyConfiguration(conf.state, conf.data.asInstanceOf[Stream[Command[V]]], conf.data))
      }
    }
  }

  private[Prover] def skipNonInit(stream: Stream[Command[V]]): Stream[Command[V]] = stream.head match {
    case com: InitialCommand[_] => stream
    case _ => skipNonInit(stream.tail)
  }
}
