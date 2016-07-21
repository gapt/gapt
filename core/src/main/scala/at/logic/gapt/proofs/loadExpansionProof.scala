package at.logic.gapt.proofs

import java.io.StringReader

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.formats.leancop.LeanCoPParser
import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.formats.verit.VeriTParser
import at.logic.gapt.proofs.expansion.{ ExpansionProof, addSymmetry }
import at.logic.gapt.proofs.resolution.{ ResolutionProof, ResolutionToExpansionProof, containsEquationalReasoning, numberOfLogicalInferencesRes, simplifyResolutionProof }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.logging.metrics

import scala.io.Source

object loadExpansionProof {

  def apply( fileName: String ): Option[ExpansionProof] = withBackgroundTheory( fileName ).map( _._1 )

  def withBackgroundTheory( fileName: String ): Option[( ExpansionProof, CutIntroduction.BackgroundTheory )] = fileName match {
    case _ if fileName endsWith ".proof_flat" =>
      VeriTParser.getExpansionProof( fileName ) map { ep => ExpansionProof( addSymmetry( ep ) ) -> CutIntroduction.BackgroundTheory.PureFOL }
    case _ if fileName contains "/leanCoP" =>
      LeanCoPParser.getExpansionProof(
        new StringReader( extractFromTSTPCommentsIfNecessary( Source.fromFile( fileName ).mkString ) )
      ) map { ExpansionProof( _ ) } map { p => p -> CutIntroduction.guessBackgroundTheory( p ) }
    case _ if fileName contains "/Prover9" =>
      val ( resProof, endSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequent(
        extractFromTSTPCommentsIfNecessary( Source.fromFile( fileName ).mkString )
      )
      Some( loadResolutionProof( resProof, endSequent ) )
    case _ => // try tstp format
      val tstpOutput = Source fromFile fileName mkString

      metrics.value( "tstp_is_cnf_ref", tstpOutput contains "CNFRefutation" )

      val ( endSequent, sketch ) = TptpProofParser parse tstpOutput
      metrics.value( "tstp_sketch_size", sketch.subProofs.size )

      RefutationSketchToResolution( sketch ) map { resProof =>
        loadResolutionProof( resProof, endSequent )
      } toOption
  }

  def extractFromTSTPCommentsIfNecessary( output: String ): String = {
    val lines = output.split( "\n" )
    if ( lines contains "%----ERROR: Could not form TPTP format derivation" )
      lines.toSeq.
        dropWhile( _ != "%----ORIGINAL SYSTEM OUTPUT" ).drop( 1 ).
        takeWhile( !_.startsWith( "%-----" ) ).dropRight( 1 ).
        map { _ substring 2 }.
        filterNot( _ startsWith "% SZS" ).
        filterNot( _ startsWith "\\n% SZS" ).
        mkString( "", "\n", "\n" )
    else
      output
  }

  private def loadResolutionProof( resProof: ResolutionProof, endSequent: HOLSequent ) = {
    metrics.value( "resinf_input", numberOfLogicalInferencesRes( simplifyResolutionProof( resProof ) ) )
    val backgroundTheory =
      if ( containsEquationalReasoning( resProof ) )
        CutIntroduction.BackgroundTheory.Equality
      else
        CutIntroduction.BackgroundTheory.PureFOL
    val expansionProof = ResolutionToExpansionProof( resProof )
    expansionProof -> backgroundTheory
  }

}
