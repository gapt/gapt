package at.logic.provers.atp.commands

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 15, 2010
 * Time: 3:10:14 PM
 * To change this template use File | Settings | File Templates.
 */

package sequents {
import _root_.at.logic.algorithms.subsumption.managers.{SimpleManager, SubsumptionManager}
import _root_.at.logic.algorithms.subsumption.SubsumptionAlgorithm
import _root_.at.logic.language.fol.FOLExpression
import _root_.at.logic.utils.ds.{Add, Remove, PublishingBufferEvent, PublishingBuffer}
import at.logic.provers.atp.commands.refinements.base.{Refinement, RefinementID}
import at.logic.provers.atp.commands.base.{ResultCommand, DataCommand, MacroCommand, InitialCommand}
  import at.logic.calculi.resolution.base.ResolutionProof
  import at.logic.calculi.lk.base.{SequentOccurrence, Sequent}
  import at.logic.provers.atp.Definitions._

  abstract class SetSequentsCommand[V <: SequentOccurrence](val clauses: Iterable[Sequent]) extends DataCommand[V]

  // set the target clause, i.e. the empty clause normally
  case class SetTargetClause[V <: SequentOccurrence](val clause: Sequent) extends DataCommand[V] {
    def apply(state: State, data: Any) = List((state += new Tuple2("targetClause", clause), data))
  }

  // tests whether the clauses list contains the target clause
  case class SearchForEmptyClauseCommand[V <: SequentOccurrence]() extends ResultCommand[V] {
    def apply(state: State, data: Any) = {
      val target = state("targetClause").asInstanceOf[Sequent]
      state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]].find(x => x.root setEquals target)
    }
  }

  case class InsertResolventCommand[V <: SequentOccurrence]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]] += data.asInstanceOf[ResolutionProof[V]]
      List((state,data))
    }
  }

  case class RefutationReachedCommand[V <: SequentOccurrence]() extends ResultCommand[V] {
    def apply(state: State, data: Any) = {
      val target = state("targetClause").asInstanceOf[Sequent]
      val d = data.asInstanceOf[ResolutionProof[V]]
      if (d.root setEquals target) Some(d)
      else None
    }
  }

  case class SequentsMacroCommand [V <: SequentOccurrence](init: InitialCommand[V], datas: Iterable[DataCommand[V]], result: ResultCommand[V])
          extends MacroCommand[V](init, datas, result) {
    def isRepeat(state: State): Boolean = {
      !state(RefinementID()).asInstanceOf[Refinement[V]].isEmpty
    }
  }

  case class IfNotExistCommand[V <: SequentOccurrence]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      val buffer = state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
      val res = data.asInstanceOf[ResolutionProof[V]]
      if (!buffer.exists(x => x.root == res.root)) List((state,data)) else List()
    }
  }
}