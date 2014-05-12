
package at.logic.provers.atp.commands.base

import at.logic.provers.atp.Definitions._
import at.logic.calculi.resolution.ResolutionProof
import at.logic.calculi.lk.base.Sequent

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
// prepend commands in data to current commands
case class PrependCommand[V <: Sequent](commands: Iterable[Command[V]]) extends Command[V]
// prepend commands in data to current commands
case class PrependOnCondCommand[V <: Sequent](cond: Function2[State, Any, Boolean], commands: Iterable[Command[V]]) extends Command[V]
// set the stream given as data as the stream in the next configuration
case class SetStreamCommand[V <: Sequent]() extends Command[V]
// this command store the configuration in state and starts a new state with the given commands in data
case class SpawnCommand[V <: Sequent]() extends Command[V]
// this commands restores the configuration from the state. it restore the processing to before the call to SpawnCommand with possible prepanding of commands
case class RestoreCommand[V <: Sequent](commands: Iterable[Command[V]]) extends Command[V]

