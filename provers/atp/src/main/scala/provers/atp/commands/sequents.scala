package at.logic.provers.atp.commands

/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 15, 2010
 * Time: 3:10:14 PM
 * To change this template use File | Settings | File Templates.
 */

package sequents {

import _root_.at.logic.algorithms.subsumption.managers._
import _root_.at.logic.algorithms.subsumption.SubsumptionAlgorithm
import _root_.at.logic.calculi.lk.base.Sequent
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.Clause
import _root_.at.logic.language.hol.{HOLFormula, HOLExpression, HOLVar}
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.types.->
import _root_.at.logic.utils.ds.{Add, Remove, PublishingBufferEvent, PublishingBuffer}
import _root_.at.logic.utils.patterns.listeners.ListenerManager
import at.logic.provers.atp.commands.base.{ResultCommand, DataCommand}
import at.logic.provers.atp.Definitions._
import at.logic.calculi.lk.base.types.FSequent

  abstract class SetSequentsCommand[V <: Sequent](val clauses: Iterable[FSequent]) extends DataCommand[V]

  // set the target clause, i.e. the empty clause normally
  case class SetTargetClause[V <: Sequent](val clause: FSequent) extends DataCommand[V] {
    def apply(state: State, data: Any) = List((state += new Tuple2("targetClause", clause), data))
  }

  // tests whether the clauses list contains the target clause
  case class SearchForEmptyClauseCommand[V <: Sequent]() extends ResultCommand[V] {
    def apply(state: State, data: Any) = {
      val target = state("targetClause").asInstanceOf[FSequent]
      state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]].find(x => fvarInvariantMSEquality(x.root, target))
    }
  }

  case class InsertResolventCommand[V <: Sequent]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      (if (state.isDefinedAt("clauses")) state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
      else {
        val pb = new PublishingBuffer[ResolutionProof[V]]
        state += new Tuple2("clauses", pb)
        pb
      }) += data.asInstanceOf[ResolutionProof[V]]
      List((state,data))
    }
  }

  // deterministically trying to match all indices (it is deterministic as it does not change the state of the different cases)
  case class ApplyOnAllPolarizedLiteralPairsCommand[V <: Sequent]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      val p = data.asInstanceOf[Tuple2[ResolutionProof[V],ResolutionProof[V]]]
      (for (i <- p._1.root.antecedent; j <- p._2.root.succedent) yield (state, List((p._2,(j,true)), (p._1, (i,false)))))  ++
      (for (i <- p._1.root.succedent; j <- p._2.root.antecedent) yield (state, List((p._1,(i,true)), (p._2,(j,false)))))
    }
  }

  case class RefutationReachedCommand[V <: Sequent]() extends ResultCommand[V] {
    def apply(state: State, data: Any) = {
      val target = state("targetClause").asInstanceOf[FSequent]
      val d = data.asInstanceOf[ResolutionProof[V]]
      if (fvarInvariantMSEquality(d.root,target)) Some(d)
      else None
    }
  }

  // tests for multiset equality while ignoring the names of the free variables
  object fvarInvariantMSEquality {
    def apply[V <: Sequent](c1: V, f2: FSequent): Boolean = {
      val f1 = (c1.antecedent.map(_.formula), c1.succedent.map(_.formula))
      val (neg,pos) = f2
      // we get all free variables from f2 and try to systematically replace those in f1
      val set1 = (f1._1 ++ f1._2).flatMap(_.subTerms).filter(e => e match {case f: HOLVar => true; case _ => false}).toSet
      val set2 = (f2._1 ++ f2._2).flatMap(_.subTerms).filter(e => e match {case f: HOLVar => true; case _ => false}).toSet
      if (set1.size != set2.size) List[FSequent]() // they cannot be equal
      // create all possible substitutions
      (for (s <- set1.toList.permutations.map(_.zip(set2)).map(x => Substitution(x.asInstanceOf[List[Pair[HOLVar,HOLExpression]]])))
        yield (f1._1.map(s(_).asInstanceOf[HOLFormula]), f1._2.map(s(_).asInstanceOf[HOLFormula]))).toList.exists(cls => {
          neg.diff(cls._1).isEmpty && pos.diff(cls._2).isEmpty && cls._1.diff(neg).isEmpty && cls._2.diff(pos).isEmpty
        })
    }
  }

  case class IfNotExistCommand[V <: Sequent]() extends DataCommand[V] {
    def apply(state: State, data: Any) = {
      val buffer = state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
      val res = data.asInstanceOf[ResolutionProof[V]]
      if (!buffer.exists(x => x.root == res.root)) List((state,data)) else List()
    }
  }

  abstract class SimpleSubsumptionCommand[V <: Sequent](val alg: SubsumptionAlgorithm) extends DataCommand[V] {
    protected def getManager(state: State): SubsumptionManager =
        if (state.isDefinedAt("simpleSubsumManager")) state("simpleSubsumManager").asInstanceOf[SubsumptionManager]
        else {
          val buffer = state("clauses").asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
          // set a listener that will listen to the buffer and fire an event (to the subsumption manager) when sequents are added or removed
          val lis = new ListenerManager[SubsumptionDSEvent] {
            buffer.addListener((x: PublishingBufferEvent[ResolutionProof[V]])=> x.ar match {
              case Add => fireEvent(SubsumptionDSEvent(SAdd, x.elem.root.toFSequent))
              case Remove => fireEvent(SubsumptionDSEvent(SRemove, x.elem.root.toFSequent))
            })
          }
          val man = new SimpleManager(lis, alg, () => buffer.iterator.map(_.root.toFSequent), f => buffer.exists(p => f(p.root.toFSequent)) , s => {buffer.filterNot(_.root.toFSequent == s); ()})
          state("simpleSubsumManager") = man
          man
    }
  }
  case class SimpleForwardSubsumptionCommand[V <: Sequent](a: SubsumptionAlgorithm) extends SimpleSubsumptionCommand[V](a) {

    def apply(state: State, data: Any) = {
      val manager = getManager(state)
      val res = data.asInstanceOf[ResolutionProof[V]]
      val res1 = res.root.toFSequent()
      if (manager.forwardSubsumption(res1)) List() else List((state,data))
    }
  }
  case class SimpleBackwardSubsumptionCommand[V <: Sequent](a: SubsumptionAlgorithm) extends SimpleSubsumptionCommand[V](a) {
    def apply(state: State, data: Any) = {
      val manager = getManager(state)
      val res = data.asInstanceOf[ResolutionProof[V]]
      val res1 = res.root.toFSequent()
      manager.backwardSubsumption(res1)
      List((state,data))
    }
  }
}
