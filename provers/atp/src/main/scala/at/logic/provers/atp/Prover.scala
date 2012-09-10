/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import _root_.at.logic.provers.atp.commands.logical.DeterministicMacroCommand
import at.logic.utils.executionModels.ndStream.{Configuration, NDStream}
import at.logic.utils.executionModels.searchAlgorithms.BFSAlgorithm
import at.logic.calculi.resolution.base.{Clause, ResolutionProof}
import at.logic.calculi.lk.base._
import collection.mutable.HashMap
import at.logic.provers.atp.commands.base._
import commands.guided.IsGuidedNotFoundCommand
import commands.refinements.simple.SimpleRefinementGetCommand
import commands.robinson.VariantsCommand

object Definitions {
  type State = HashMap[String, Any]
}

import Definitions._

object Main {
  import commands.base._
  import commands.ui._
  import commands.sequents._
  import commands.robinson._
  import _root_.at.logic.provers.atp.commands.logical.DeterministicAndCommand
  import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
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
    val prover = new Prover[Clause]{}
    prover.refute(Stream.cons(SetClausesCommand((new FileReader(args(0)) with SimpleResolutionParserFOL).getClauseList), stream)).next
  }
}

class ProverException(msg: String) extends Exception(msg)

trait Prover[V <: Sequent] extends at.logic.utils.logging.Logger {
  
  def refute(commands: Stream[Command[V]]) : NDStream[ResolutionProof[V]] = {
    println("\nrefute")
    new NDStream(new MyConfiguration(new State(), commands, ()), myFun) with BFSAlgorithm
  }
  
  private[Prover] class MyConfiguration(val state: State, val commands: Stream[Command[V]], val data: Any, val result: Option[ResolutionProof[V]]) extends Configuration[ResolutionProof[V]] {
    def this(state: State, commands: Stream[Command[V]], data: Any) = this(state, commands, data, None)
    def isTerminal = result != None
  }

  private[Prover] def myFun(c: Configuration[ResolutionProof[V]]): Iterable[Configuration[ResolutionProof[V]]] = {
    val conf = c.asInstanceOf[MyConfiguration]
//    Console.println("debug -- command: " + Console.RED + conf.commands.head.getClass + Console.RESET +", data: " + conf.data + ", next Command: " + conf.commands.tail.head.getClass)
    if (conf.commands.isEmpty) {
      println("\nconf.commands.isEmpty !\n")
      List()
    }
    else {
      //if (!conf.commands.head.toString.matches("(VariantsCommand|IsGuidedNotFoundCommand|SimpleRefinementGetCommand|ClauseFactorCommand).*"))
          println("\nProver Executing command: "+Console.RED+conf.commands.head.getClass+Console.RESET+" :: "+conf.commands.head.toString+"\n")

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
