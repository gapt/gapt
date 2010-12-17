package at.logic.provers.atp.commands.refinements

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 17, 2010
 * Time: 3:40:56 PM
 * To change this template use File | Settings | File Templates.
 */

package base {
import at.logic.calculi.lk.base.SequentOccurrence
import at.logic.calculi.resolution.base.ResolutionProof
import at.logic.utils.ds.{PublishingBuffer, PublishingBufferEvent, Remove, Add}

  object RefinementID {
    def apply() = "Refinement"
  }

  abstract class Refinement[V <: SequentOccurrence](protected val clauses: PublishingBuffer[ResolutionProof[V]]) {
    clauses.addListener((x: PublishingBufferEvent[ResolutionProof[V]])=> x.ar match {
      case Remove => removeClause(x.elem)
      case Add => addClause(x.elem)
    })

    def isEmpty: Boolean
    protected def addClause(s: ResolutionProof[V]): Unit
    protected def removeClause(s: ResolutionProof[V]): Unit
  }
}