/**
 * Description: An abstract prover
 */

package at.logic.provers.atp

import at.logic.utils.executionModels.ndStream.{Configuration, NDStream}
import at.logic.utils.executionModels.searchAlgorithms.BFSAlgorithm
import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import collection.mutable.HashMap
import at.logic.provers.atp.commands.base._

object Definitions {
  type State = HashMap[String, Any]
}

import Definitions._

trait Prover[V <: SequentOccurrence] extends at.logic.utils.logging.Logger {
  
  def refute(commands: Stream[Command[V]]) : NDStream[ResolutionProof[V]] = {
    new NDStream(new MyConfiguration(new State(), commands, ()), myFun) with BFSAlgorithm
  }
  
  private[Prover] class MyConfiguration(val state: State, val commands: Stream[Command[V]], val data: Any, val result: Option[ResolutionProof[V]]) extends Configuration[ResolutionProof[V]] {
    def this(state: State, commands: Stream[Command[V]], data: Any) = this(state, commands, data, None)
    def isTerminal = result != None
  }

  private[Prover] def myFun(c: Configuration[ResolutionProof[V]]): Iterable[Configuration[ResolutionProof[V]]] = {
    val conf = c.asInstanceOf[MyConfiguration]
    if (conf.commands.isEmpty) List()
    else {
      conf.commands.head match {
        case com: InitialCommand[_] => com(conf.state).map(x => new MyConfiguration(x._1, conf.commands.tail, x._2))
        case com: DataCommand[_] => {
          val res = com(conf.state, conf.data)
          if (res.isEmpty) List(new MyConfiguration(conf.state, skipNonInit(conf.commands.tail), ()))
          else res.map(x => new MyConfiguration(x._1, conf.commands.tail, x._2))
        }
        case com: ResultCommand[_] => List(new MyConfiguration(conf.state, conf.commands.tail, conf.data, com(conf.state, conf.data)))
        case com: MacroCommand[_] => {
          val res = com(conf.state)
          res._1.map(x => new MyConfiguration(x._1, conf.commands.tail, conf.data, x._2)) ++
          (if (res._2) List(new MyConfiguration(conf.state, conf.commands.tail, conf.data)) else List())
        }
        case com: BranchCommand[_] => com.commands.map(x => new MyConfiguration(conf.state, x ++ conf.commands.tail, conf.data))
      }
    }
  }

  private[Prover] def skipNonInit(stream: Stream[Command[V]]): Stream[Command[V]] = stream.head match {
    case com: InitialCommand[_] => stream
    case _ => skipNonInit(stream.tail)
  }
}