package at.logic.gapt.provers.atp.commands.replay

/**
 * this file contains command for a guided search using ids for clauses,as for example when parsing the output of theorem provers and using the rules from there
 */
import at.logic.gapt.proofs.lk.subsumption.StillmanSubsumptionAlgorithmFOL
import at.logic.gapt.expr.fol.{ FOLMatchingAlgorithm, FOLUnificationAlgorithm }
import at.logic.gapt.proofs.resolution.{ ResolutionProof, OccClause }
import at.logic.gapt.proofs.resolution.robinson.{ RobinsonResolutionProof }
import at.logic.gapt.proofs.lk.base.{ OccSequent, HOLSequent }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.resolution.robinson.InitialClause._
import at.logic.gapt.provers.atp.Definitions._
import at.logic.gapt.provers.atp.Prover
import at.logic.gapt.utils.ds.PublishingBuffer

import at.logic.gapt.provers.atp.commands.guided.{ AddGuidedResolventCommand, GetGuidedClausesCommand, IsGuidedNotFoundCommand, SetGuidedFoundCommand }
import at.logic.gapt.provers.atp.commands.sequents._
import at.logic.gapt.provers.atp.commands.base._
import at.logic.gapt.provers.atp.commands.robinson._
import at.logic.gapt.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.gapt.provers.atp.commands.refinements.base.SequentsMacroCommand
import at.logic.gapt.provers.atp.commands.refinements.simple.SimpleRefinementGetCommand
import at.logic.gapt.utils.logging.Logger
import org.slf4j.LoggerFactory

import scala.collection.mutable.{ Map => MMap }

//TODO: i'm not sure, why the other publishing buffers are robinsonproofs -- since we cannot upcast here and the gmap
// only holds resolution proofs, i'm not sure what is better
case class SetClauseWithProofCommand( clauses: Iterable[ResolutionProof[OccClause]] ) extends DataCommand[OccClause] with Logger {
  def apply( state: State, data: Any ) = {
    val pb = new PublishingBuffer[ResolutionProof[OccClause]]
    clauses.foreach( x => pb += x )
    debug( s"clauses ++= $clauses" )
    List( ( state += new Tuple2( "clauses", pb ), data ) )
  }
}

case class SetTargetClause2[V <: OccSequent]( val clause: OccClause ) extends DataCommand[V] {
  def apply( state: State, data: Any ) = List( ( state += new Tuple2( "targetClause", clause.toHOLSequent ), data ) )
}

case object PrintStateCommand extends DataCommand[OccClause] with Logger {
  override def loggerName = "ReplayLogger"

  def apply( state: State, data: Any ): Iterable[( State, Any )] = {
    debug( "state: " + state )
    debug( "data:" + data )
    List( ( state, data ) )
  }
}

case class ReplayCommand( parentIds: Iterable[String], id: String, cls: HOLSequent ) extends DataCommand[OccClause] with Logger {
  override def loggerName = "ReplayLogger"

  def apply( state: State, data: Any ) = {
    import Stream.cons
    //get guided clauses mapping from id to resolution proof of id
    debug( "ReplayCommand: Target clause :" + id + " from " + parentIds.toList )
    val gmap = state( "gmap" ).asInstanceOf[MMap[String, ResolutionProof[OccClause]]]
    // val nLine = sys.props("line.separator")
    //println( nLine + "Data="+data )
    //println( nLine + "Target clause="+cls )

    val gproofs = ( parentIds.toList ).filterNot( _ == "-1" ) map gmap

    //val target : Clause = if (id == "-1") Clause(Nil,Nil) else Clause(cls.antecedent, cls.succedent)
    debug( s"Trying to prove $cls from:" )
    gproofs foreach ( x => debug( x.root.toString ) )

    //initialize new prover to spawn -- same as proveFOL in cli
    val prover = new Prover[OccClause] {}

    def stream1: Stream[Command[OccClause]] = cons( SequentsMacroCommand[OccClause](
      SimpleRefinementGetCommand[OccClause],
      List(
        VariantsCommand,
        DeterministicAndCommand[OccClause]( (
          List( ApplyOnAllPolarizedLiteralPairsCommand[OccClause], ResolveCommand( FOLUnificationAlgorithm ), FactorCommand( FOLUnificationAlgorithm ) ),
          List( ParamodulationCommand( FOLUnificationAlgorithm ) )
        ) ),
        SimpleForwardSubsumptionCommand[OccClause]( StillmanSubsumptionAlgorithmFOL ),
        SimpleBackwardSubsumptionCommand[OccClause]( StillmanSubsumptionAlgorithmFOL ),
        //        PrintStateCommand,
        InsertResolventCommand[OccClause]
      ),
      RefutationReachedCommand[OccClause]
    ), stream1 )
    //RefutationReachedCommand is replaced by SubsumedTargedReachedCommand
    //        SubsumedTargedReachedCommand[Clause]), stream1)

    //    prover.refute(cons(SetClauseWithProofCommand(gproofs), cons(  SetTargetClause(cls), cons( SubsumedTargedSetFromClauseSetCommand(), stream1)))).next match {
    prover.refute( cons( SetClauseWithProofCommand( gproofs ), cons( SetTargetClause( cls ), stream1 ) ) ).next match {
      case Some( r ) =>
        //println("Found a refutation: "+r.toString)
        gmap( id ) = r //add new id to the guidance map
        List( ( state, r ) )

      case _ => //println("Replay failed!");
        List() //need to signal failure!
    }
  }

  override def toString = s"ReplayCommand New($parentIds, $id, $cls)"
}

// we dont have subsumption as it might prevent reaching the exact clause we look for
case class OldReplayCommand( parentIds: Iterable[String], id: String, cls: HOLSequent ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("replay: " + parentIds + " - " + id + " - target: " + cls)
    def stream1: Stream[Command[OccClause]] =
      Stream.cons(
        SimpleRefinementGetCommand[OccClause],
        Stream.cons(
          VariantsCommand,
          Stream.cons(
            ClauseFactorCommand( FOLUnificationAlgorithm ),
            Stream.cons(
              DeterministicAndCommand[OccClause]( (
                List( ApplyOnAllPolarizedLiteralPairsCommand[OccClause], ResolveCommand( FOLUnificationAlgorithm ) ),
                List( ParamodulationCommand( FOLUnificationAlgorithm ) )
              ) ),
              Stream.cons(
                IsGuidedNotFoundCommand,
                Stream.cons(
                  InsertResolventCommand[OccClause],
                  Stream.cons(
                    PrependOnCondCommand[OccClause](
                      ( s: State, d: Any ) => {
                        val gtf = s.isDefinedAt( "guided_target_found" )
                        val fveq = fvarInvariantMSEquality( d.asInstanceOf[RobinsonResolutionProof].root, s( "targetClause" ).asInstanceOf[HOLSequent] )
                        if ( fveq ) s( "guided_target_found" ) = true
                        !gtf && fveq
                      },
                      RestoreCommand[OccClause]( AddGuidedResolventCommand( id ) :: InsertResolventCommand[OccClause] :: RefutationReachedCommand[OccClause] :: Nil ) :: Nil
                    ),
                    stream1
                  )
                )
              )
            )
          )
        )
      )
    List( ( state, Stream.cons( GetGuidedClausesCommand( parentIds ), Stream.cons( SetClausesFromDataCommand, Stream.cons( SetTargetClause( cls ), stream1 ) ) ) ) )
  }

  override def toString = "ReplayCommand(" + parentIds + ", " + id + ", " + cls + ")"
}
