
package at.logic.provers.atp.commands.refinements.base

import at.logic.provers.atp.commands.base.{InitialCommand, DataCommand, ResultCommand}
import at.logic.provers.atp.commands.logical.DeterministicMacroCommand
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.resolution.ResolutionProof
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

