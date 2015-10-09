package at.logic.gapt.provers.atp

import java.io.IOException

import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.resolutionOld.{ OccClause, ResolutionProof }
import at.logic.gapt.provers.atp.commands.Prover9InitCommand
import at.logic.gapt.provers.atp.commands.base.SetStreamCommand
import at.logic.gapt.provers.atp.commands.sequents.SetTargetClause

object replay {

  def apply( clauses: Seq[HOLSequent] ): Option[ResolutionProof[OccClause]] =
    try {
      new Prover[OccClause] {}.
        refute( Stream( SetTargetClause( HOLSequent( List(), List() ) ), Prover9InitCommand( clauses ), SetStreamCommand() ) ).next
    } catch {
      case e: IOException => throw new IOException( "Prover9 is not installed: " + e.getMessage() )
    }

  def apply( clauses: List[OccSequent] ): Option[ResolutionProof[OccClause]] =
    try {
      new Prover[OccClause] {}.
        refute( Stream( SetTargetClause( HOLSequent( List(), List() ) ), Prover9InitCommand( ( clauses map ( ( x: OccSequent ) => x.toHOLSequent ) ).toList ), SetStreamCommand() ) ).next
    } catch {
      case e: IOException => throw new IOException( "Prover9 is not installed: " + e.getMessage() )
    }
}
