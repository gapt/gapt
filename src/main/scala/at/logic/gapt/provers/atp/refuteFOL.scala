package at.logic.gapt.provers.atp

import at.logic.gapt.expr.fol.FOLUnificationAlgorithm
import at.logic.gapt.proofs.resolutionOld._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.subsumption.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.provers.atp.commands.base.Command
import at.logic.gapt.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.gapt.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.gapt.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import at.logic.gapt.provers.atp.commands.robinson._
import at.logic.gapt.provers.atp.commands.sequents._
import at.logic.gapt.provers.atp.commands.ui.{ PromptTerminal, getTwoClausesFromUICommand }

object refuteFOL {

  def stream1: Stream[Command[OccClause]] = Stream.cons( SequentsMacroCommand[OccClause](
    SimpleRefinementGetCommand[OccClause],
    List( VariantsCommand, DeterministicAndCommand[OccClause](
      List( ApplyOnAllPolarizedLiteralPairsCommand[OccClause], ResolveCommand( FOLUnificationAlgorithm ), FactorCommand( FOLUnificationAlgorithm ) ),
      List( ParamodulationCommand( FOLUnificationAlgorithm ) )
    ),
      SimpleForwardSubsumptionCommand[OccClause]( StillmanSubsumptionAlgorithmFOL ),
      SimpleBackwardSubsumptionCommand[OccClause]( StillmanSubsumptionAlgorithmFOL ),
      InsertResolventCommand[OccClause] ),
    RefutationReachedCommand[OccClause]
  ), stream1 )

  def stream: Stream[Command[OccClause]] = Stream.cons( SetTargetClause( HOLSequent( List(), List() ) ), Stream.cons( SearchForEmptyClauseCommand[OccClause], stream1 ) )

  def apply( clauses: Seq[HOLSequent] ): Option[ResolutionProof[OccClause]] =
    new Prover[OccClause] {}.
      refute( Stream.cons( SetClausesCommand( clauses ), stream ) ).next
}

object refuteFOLI {

  def stream1: Stream[Command[OccClause]] = Stream.cons(
    getTwoClausesFromUICommand[OccClause]( PromptTerminal.GetTwoClauses ),
    Stream.cons(
      VariantsCommand,
      Stream.cons(
        DeterministicAndCommand[OccClause]( (
          List( ApplyOnAllPolarizedLiteralPairsCommand[OccClause], ResolveCommand( FOLUnificationAlgorithm ), FactorCommand( FOLUnificationAlgorithm ) ),
          List( ParamodulationCommand( FOLUnificationAlgorithm ) )
        ) ),
        Stream.cons(
          SimpleForwardSubsumptionCommand[OccClause]( StillmanSubsumptionAlgorithmFOL ),
          Stream.cons(
            SimpleBackwardSubsumptionCommand[OccClause]( StillmanSubsumptionAlgorithmFOL ),
            Stream.cons(
              InsertResolventCommand[OccClause],
              Stream.cons( RefutationReachedCommand[OccClause], stream1 )
            )
          )
        )
      )
    )
  )

  def stream: Stream[Command[OccClause]] = Stream.cons( SetTargetClause( HOLSequent( List(), List() ) ), Stream.cons( SearchForEmptyClauseCommand[OccClause], stream1 ) )

  def apply( clauses: Seq[HOLSequent] ): Option[ResolutionProof[OccClause]] =
    new Prover[OccClause] {}.
      refute( Stream.cons( SetClausesCommand( clauses ), stream ) ).next
}

