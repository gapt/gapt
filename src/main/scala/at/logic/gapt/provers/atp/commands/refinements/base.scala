
package at.logic.gapt.provers.atp.commands.refinements.base

import at.logic.gapt.provers.atp.commands.base.{ InitialCommand, DataCommand, ResultCommand }
import at.logic.gapt.provers.atp.commands.logical.DeterministicMacroCommand
import at.logic.gapt.proofs.lk.base.OccSequent
import at.logic.gapt.proofs.resolutionOld.ResolutionProof
import at.logic.gapt.utils.ds.{ PublishingBuffer, PublishingBufferEvent, Remove, Add }
import at.logic.gapt.provers.atp.Definitions._

object RefinementID {
  def apply() = "Refinement"
}

abstract class Refinement[V <: OccSequent]( protected val clauses: PublishingBuffer[ResolutionProof[V]] ) {
  clauses.addListener( ( x: PublishingBufferEvent[ResolutionProof[V]] ) => x.ar match {
    case Remove => removeClause( x.elem )
    case Add    => addClause( x.elem )
  } )

  def isEmpty: Boolean
  protected def addClause( s: ResolutionProof[V] ): Unit
  protected def removeClause( s: ResolutionProof[V] ): Unit
}

case class SequentsMacroCommand[V <: OccSequent]( init: InitialCommand[V], datas: Iterable[DataCommand[V]], result: ResultCommand[V] )
    extends DeterministicMacroCommand[V]( init, datas, result ) {
  def isRepeat( state: State ): Boolean = {
    !state( RefinementID() ).asInstanceOf[Refinement[V]].isEmpty
  }
}

