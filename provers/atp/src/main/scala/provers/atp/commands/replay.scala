package at.logic.provers.atp.commands

/**
 * this file contains command for a guided search using ids for clauses,as for example when parsing the output of theorem provers and using the rules from there
 */
package replay {

import _root_.at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import _root_.at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
import _root_.at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.{RobinsonResolutionProof, Clause}
import _root_.at.logic.language.fol.{FOLExpression, FOLFormula}
import _root_.at.logic.language.hol.HOLFormula
import _root_.at.logic.provers.atp.commands.sequents._
import at.logic.calculi.lk.base.types.FSequent
import _root_.at.logic.provers.atp.Definitions._
import refinements.simple.SimpleRefinementGetCommand
import guided.{AddGuidedResolventCommand, GetGuidedClausesCommand,IsGuidedNotFoundCommand,SetGuidedFoundCommand}
import sequents.RefutationReachedCommand._
import base.BranchCommand._
import robinson.ParamodulationCommand._
import robinson._
import base._
import logical.DeterministicAndCommand

  // we dont have subsumption as it might prevent reaching the exact clause we look for
  case class ReplayCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      //println("replay: " + parentIds + " - " + id + " - target: " + cls)
      def stream1: Stream[Command[Clause]] =
        Stream.cons(SimpleRefinementGetCommand[Clause],
          Stream.cons(VariantsCommand,
          Stream.cons(ClauseFactorCommand(FOLUnificationAlgorithm),
          Stream.cons(DeterministicAndCommand[Clause]((
            List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm)),
            List(ParamodulationCommand(FOLUnificationAlgorithm)))),
          Stream.cons(IsGuidedNotFoundCommand,
          Stream.cons(InsertResolventCommand[Clause],
          Stream.cons(PrependOnCondCommand[Clause](
            (s: State,d: Any) => fvarInvariantMSEquality(d.asInstanceOf[RobinsonResolutionProof].root, s("targetClause").asInstanceOf[FSequent]) ,
              SetGuidedFoundCommand::RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil),
          stream1))))))
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand, Stream.cons(SetTargetClause(cls), stream1)))))
    }
  }

  // we dont have subsumption as it might prevent reaching the exact clause we look for
  case class ReplayOnlyParamodulationCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      //println("replay: " + parentIds + " - " + id)
      def stream1: Stream[Command[Clause]] =
        Stream.cons(SimpleRefinementGetCommand[Clause],
          Stream.cons(VariantsCommand,
          Stream.cons(ParamodulationCommand(FOLUnificationAlgorithm),
          Stream.cons(IsGuidedNotFoundCommand,
          Stream.cons(InsertResolventCommand[Clause],
          Stream.cons(PrependOnCondCommand[Clause](
            (s: State,d: Any) => fvarInvariantMSEquality(d.asInstanceOf[RobinsonResolutionProof].root, s("targetClause").asInstanceOf[FSequent]) ,
              SetGuidedFoundCommand::RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil),
          stream1)))))
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand, Stream.cons(SetTargetClause(cls), stream1)))))
    }
  }

  // we dont have subsumption as it might prevent reaching the exact clause we look for
  case class ReplayNoParamodulationCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      //println("replay: " + parentIds + " - " + id)
      def stream1: Stream[Command[Clause]] =
        Stream.cons(SimpleRefinementGetCommand[Clause],
          Stream.cons(VariantsCommand,
          Stream.cons(ClauseFactorCommand(FOLUnificationAlgorithm),
          Stream.cons(ApplyOnAllPolarizedLiteralPairsCommand[Clause],
          Stream.cons(ResolveCommand(FOLUnificationAlgorithm),
          Stream.cons(IsGuidedNotFoundCommand,
          Stream.cons(InsertResolventCommand[Clause],
          Stream.cons(PrependOnCondCommand[Clause](
            (s: State,d: Any) => fvarInvariantMSEquality(d.asInstanceOf[RobinsonResolutionProof].root, s("targetClause").asInstanceOf[FSequent]) ,
              SetGuidedFoundCommand::RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil),
          stream1)))))))
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand, Stream.cons(SetTargetClause(cls), stream1)))))
    }
  }
}
