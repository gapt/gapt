package at.logic.provers.atp.commands

import at.logic.calculi.lk.base._
import at.logic.calculi.resolution.base._
import at.logic.provers.atp.Definitions._

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 13, 2010
 * Time: 12:56:29 PM
 * To change this template use File | Settings | File Templates.
 */

package base {
    // exceptions
  object CommandsExhaustedException extends Exception

/**
 * Commands should return empty list in case they dont have an output and throw an exception in case they input is illegal
 * (i.e. the output of the previous command is not compatible with the expected input of this command )
 */
  abstract class Command[V <: SequentOccurrence] {
    def isSubsequentOf(c: Command[V]): Boolean = true // override for specific commands
  }
  //abstract class DataCommand[V <: SequentOccurrence] extends Command[V] with Function2[State, Any, Tuple2[State, Any]]
  abstract class DataCommand[V <: SequentOccurrence] extends Command[V] with Function2[State, Any, Iterable[Tuple2[State, Any]]]
  // initial means a command that does not expect a data, when a data command returns an empty list the prover search for the enxt initial command
  abstract class InitialCommand[V <: SequentOccurrence] extends Command[V] with Function1[State, Iterable[Tuple2[State, Any]]]
  abstract class ResultCommand[V <: SequentOccurrence] extends Command[V] with Function2[State, Any, Option[ResolutionProof[V]]]

  // in order to keep the ndStream stack relatively small, we concatenate a list of commands in one configuration. This is clearly a deterministic command
  // for non determinism, one must create a macro command that still enter all non-deterministic cases into the ndStream
  abstract class MacroCommand [V <: SequentOccurrence](init: InitialCommand[V], datas: Iterable[DataCommand[V]], result: ResultCommand[V]) extends Command[V] with
          Function1[State, Tuple2[Iterable[Tuple2[State, Option[ResolutionProof[V]]]], Boolean]] {
    def apply(state: State) = (init(state).map(_._2).flatMap(x => getResults(state, datas,x::Nil)).map(y => (state,result(state,y))).filter(z => z._2 != None), isRepeat(state))
    private def getResults(state: State, datas: Iterable[DataCommand[V]], values: Iterable[Any]): Iterable[Any] = if (datas.isEmpty) values
      else getResults(state, datas.tail, values.flatMap(x => datas.head(state, x).map(_._2)))
    // tells the Prover if should terminate this branch or not. In deterministic execution only one none result configuration exists in ndStream and terminating it
    // should correspond to the possibility of having more clauses to resolve on. If using refinements then it corresponds if all pairs were matched already.
    def isRepeat(state: State): Boolean
  }
}