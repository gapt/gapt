package at.logic.provers.atp.commands

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 20, 2010
 * Time: 5:12:03 PM
 * To change this template use File | Settings | File Templates.
 */

package logical {
import _root_.at.logic.calculi.lk.base.Sequent
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.provers.atp.commands.base.{Command, ResultCommand, InitialCommand, DataCommand}
import at.logic.provers.atp.Definitions._

  // using the same state, therefore deterministic
  case class DeterministicAndCommand[V <: Sequent](commands: Tuple2[Iterable[DataCommand[V]],Iterable[DataCommand[V]]]) extends DataCommand[V] {
    def apply(state: State, data: Any) =
      ((commands._1.foldLeft(List((state,data)))((res,com) => res.flatMap(y => com(state,y._2)))) ++
      (commands._2.foldLeft(List((state,data)))((res,com) => res.flatMap(y => com(state,y._2)))))
  }

  // in order to keep the ndStream stack relatively small, we concatenate a list of commands in one configuration. This is clearly a deterministic command
  // for non determinism, one must create a macro command that still enter all non-deterministic cases into the ndStream
  // using the same state, therefore deterministic
  abstract class DeterministicMacroCommand [V <: Sequent](init: InitialCommand[V], datas: Iterable[DataCommand[V]], result: ResultCommand[V]) extends Command[V] with
          Function1[State, Tuple2[Iterable[Tuple2[State, Option[ResolutionProof[V]]]], Boolean]] {
    def apply(state: State) = (init(state).map(_._2).flatMap(x => getResults(state, datas,x::Nil)).map(y => (state,result(state,y))).filter(z => z._2 != None), isRepeat(state))
    private def getResults(state: State, datas: Iterable[DataCommand[V]], values: Iterable[Any]): Iterable[Any] = if (datas.isEmpty) values
      else getResults(state, datas.tail, values.flatMap(x => datas.head(state, x).map(_._2)))
    // tells the Prover if should terminate this branch or not. In deterministic execution only one none result configuration exists in ndStream and terminating it
    // should correspond to the possibility of having more clauses to resolve on. If using refinements then it corresponds if all pairs were matched already.
    def isRepeat(state: State): Boolean
  }
}
