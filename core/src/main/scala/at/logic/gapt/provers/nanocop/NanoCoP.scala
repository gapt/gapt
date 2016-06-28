package at.logic.gapt.provers.nanocop

import java.io.IOException

import at.logic.gapt.expr.Substitution
import at.logic.gapt.expr.hol.skolemizeFormula
import at.logic.gapt.formats.nanocop.{ NanocopParser, nanocopToExpansion }
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, tptpToString }
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, eliminateMerges, expansionFromNNF }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.{ OneShotProver, groundFreeVariables, renameConstantsToFi }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.utils.{ ExternalProgram, runProcess }
import at.logic.gapt.utils.ScalazHelpers._

class NanoCoP extends OneShotProver with ExternalProgram {
  override def getExpansionProof( seq: HOLSequent ): Option[ExpansionProof] =
    groundFreeVariables.wrap( seq ) { seq =>
      renameConstantsToFi.wrap( seq )( ( _, seq: HOLSequent ) => {
        val ( skSeq, skDefs ) = skolemizeFormula.withDefs( seq )
        val input = new tptpToString( sugar = false, alwaysParens = true ).tptpFile( TPTPFOLExporter( skSeq ) )
        val output = runProcess.withTempInputFile( Seq( "nanocop" ), input ).split( "\n" )
        if ( output exists { _ endsWith " is a Non-Theorem" } ) {
          None
        } else {
          val ( shallow, deep ) = NanocopParser.parseString( output.filter( _.startsWith( "[" ) ).mkString )
          val nnfExpansion = nanocopToExpansion( shallow, deep )
          val skolemizedExpansion = eliminateMerges.unsafe( expansionFromNNF( List( nnfExpansion ), skSeq ) )
          val expansion = for ( ( sh, et ) <- seq zip skolemizedExpansion ) yield skDefs.addSkolemInfs( sh, Substitution(), et )
          Some( ExpansionProof( expansion ) )
        }
      } )
    }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    getExpansionProof( seq ) map { ExpansionProofToLK( _ ).get }

  override val isInstalled: Boolean =
    try runProcess.withExitValue( Seq( "nanocop" ) )._1 == 2
    catch { case _: IOException => false }
}

object NanoCoP extends NanoCoP