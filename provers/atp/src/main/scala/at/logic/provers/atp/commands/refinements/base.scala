package at.logic.provers.atp.commands.refinements

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 17, 2010
 * Time: 3:40:56 PM
 * To change this template use File | Settings | File Templates.
 */

package base {
import _root_.at.logic.provers.atp.commands.base.{InitialCommand, DataCommand, ResultCommand}
import _root_.at.logic.provers.atp.commands.logical.DeterministicMacroCommand
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.utils.ds.{PublishingBuffer, PublishingBufferEvent, Remove, Add}
import at.logic.provers.atp.Definitions._
  
  object RefinementID {
    def apply() = "Refinement"
  }

  abstract class Refinement[V <: Sequent](protected val clauses: PublishingBuffer[ResolutionProof[V]]) {
    clauses.addListener((x: PublishingBufferEvent[ResolutionProof[V]])=> x.ar match {
      case Remove => removeClause(x.elem)
      case Add => addClause(x.elem)
    })

    def isEmpty: Boolean
    protected def addClause(s: ResolutionProof[V]): Unit
    protected def removeClause(s: ResolutionProof[V]): Unit
  }

  case class SequentsMacroCommand [V <: Sequent](init: InitialCommand[V], datas: Iterable[DataCommand[V]], result: ResultCommand[V])
          extends DeterministicMacroCommand[V](init, datas, result) {
    def isRepeat(state: State): Boolean = {
      !state(RefinementID()).asInstanceOf[Refinement[V]].isEmpty
    }
  }
}
