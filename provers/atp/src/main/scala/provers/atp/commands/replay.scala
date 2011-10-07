package at.logic.provers.atp.commands

/**
 * this file contains command for a guided search using ids for clauses,as for example when parsing the output of theorem provers and using the rules from there
 */
package replay {

import _root_.at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import _root_.at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
import _root_.at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.Clause
import _root_.at.logic.language.fol.{FOLExpression, FOLFormula}
import _root_.at.logic.provers.atp.commands.sequents.SimpleBackwardSubsumptionCommand
import _root_.at.logic.provers.atp.commands.sequents.SimpleForwardSubsumptionCommand
import at.logic.calculi.lk.base.types.FSequent
import _root_.at.logic.provers.atp.Definitions._
import refinements.simple.SimpleRefinementGetCommand
import guided.{AddGuidedResolventCommand, GetGuidedClausesCommand}
import sequents.RefutationReachedCommand._
import sequents.{RefutationReachedCommand, SetTargetClause, InsertResolventCommand, ApplyOnAllPolarizedLiteralPairsCommand}
import base.BranchCommand._
import robinson.ParamodulationCommand._
import robinson._
import base._
import logical.DeterministicAndCommand

case class ReplayCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      def stream1: Stream[Command[Clause]] =
        Stream.cons(SimpleRefinementGetCommand[Clause],
          Stream.cons(VariantsCommand,
          Stream.cons(DeterministicAndCommand[Clause]((
            List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
            List(ParamodulationCommand(FOLUnificationAlgorithm)))),
          Stream.cons(InsertResolventCommand[Clause],
          Stream.cons(PrependOnCondCommand[Clause](
            (s: State,d: Any) =>  d.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals s("targetClause").asInstanceOf[FSequent], RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil),
          stream1))))
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand,Stream.cons(SetTargetClause(cls), stream1)))))
    }
  }

// does not add intemediate resolvents and try reaching the target only once
case class OneStepReplayCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      def stream1: Stream[Command[Clause]] =
        Stream(SimpleRefinementGetCommand[Clause],
          VariantsCommand,
          DeterministicAndCommand[Clause]((
            List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
            List(ParamodulationCommand(FOLUnificationAlgorithm)))),
          InsertResolventCommand[Clause],
          PrependOnCondCommand[Clause](
            (s: State,d: Any) =>  d.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals s("targetClause").asInstanceOf[FSequent], RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil
          )
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand,Stream.cons(SetTargetClause(cls), stream1)))))
    }
  }

  case class ReplayNoParamodulationCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      println("replay: " + parentIds + " - " + id + " - "  + cls)
      def stream1: Stream[Command[Clause]] =
        Stream.cons(SimpleRefinementGetCommand[Clause],
          Stream.cons(VariantsCommand,
          Stream.cons(ApplyOnAllPolarizedLiteralPairsCommand[Clause],
          Stream.cons(ResolveCommand(FOLUnificationAlgorithm),
          Stream.cons(FactorCommand(FOLUnificationAlgorithm),
          Stream.cons(SimpleForwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
          Stream.cons(SimpleBackwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
          Stream.cons(InsertResolventCommand[Clause],
          Stream.cons(PrependOnCondCommand[Clause](
            (s: State,d: Any) =>  {println ("ReplayCommand cond: " + d.asInstanceOf[ResolutionProof[Clause]].root + " meq " + s("targetClause").asInstanceOf[FSequent]); d.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals s("targetClause").asInstanceOf[FSequent]},
              RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil),
          stream1))))))))
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand,Stream.cons(SetTargetClause(cls), stream1)))))
    }
  }
}
