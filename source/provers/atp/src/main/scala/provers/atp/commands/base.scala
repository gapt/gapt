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
  abstract class Command[V <: Sequent] {
    def isSubsequentOf(c: Command[V]): Boolean = true // override for specific commands
  }
  //abstract class DataCommand[V <: Sequent] extends Command[V] with Function2[State, Any, Tuple2[State, Any]]
  abstract class DataCommand[V <: Sequent] extends Command[V] with Function2[State, Any, Iterable[Tuple2[State, Any]]]
  // initial means a command that does not expect a data, when a data command returns an empty list the prover search for the enxt initial command
  abstract class InitialCommand[V <: Sequent] extends Command[V] with Function1[State, Iterable[Tuple2[State, Any]]]
  abstract class ResultCommand[V <: Sequent] extends Command[V] with Function2[State, Any, Option[ResolutionProof[V]]]

  case class BranchCommand[V <: Sequent](commands: Iterable[Stream[Command[V]]]) extends Command[V]
}
