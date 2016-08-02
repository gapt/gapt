package at.logic.gapt.proofs

import java.io.StringReader

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.formats.{ StringInputFile, InputFile }
import at.logic.gapt.formats.leancop.LeanCoPParser
import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.formats.verit.VeriTParser
import at.logic.gapt.proofs.expansion.{ ExpansionProof, addSymmetry }
import at.logic.gapt.proofs.resolution.{ ResolutionProof, ResolutionToExpansionProof, containsEquationalReasoning, numberOfLogicalInferencesRes, simplifyResolutionProof }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.logging.metrics

object loadExpansionProof {

  def apply( file: InputFile ): Option[ExpansionProof] = withBackgroundTheory( file ).map( _._1 )

  def withBackgroundTheory( file: InputFile ): Option[( ExpansionProof, CutIntroduction.BackgroundTheory )] = file.fileName match {
    case fileName if fileName endsWith ".proof_flat" =>
      VeriTParser.getExpansionProof( fileName ) map { ep => ExpansionProof( addSymmetry( ep ) ) -> CutIntroduction.BackgroundTheory.PureFOL }
    case fileName if fileName contains "/leanCoP" =>
      LeanCoPParser.getExpansionProof(
        extractFromTSTPCommentsIfNecessary( file )
      ) map { ExpansionProof( _ ) } map { p => p -> CutIntroduction.guessBackgroundTheory( p ) }
    case fileName if fileName contains "/Prover9" =>
      val ( resProof, endSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequent( file )
      Some( loadResolutionProof( resProof, endSequent ) )
    case _ => // try tstp format
      val tstpOutput = file.read

      metrics.value( "tstp_is_cnf_ref", tstpOutput contains "CNFRefutation" )

      val ( endSequent, sketch ) = TptpProofParser.parse( StringInputFile( tstpOutput ), ignoreStrongQuants = true )
      metrics.value( "tstp_sketch_size", sketch.subProofs.size )

      RefutationSketchToResolution( sketch ) map { resProof =>
        loadResolutionProof( resProof, endSequent )
      } toOption
  }

  def extractFromTSTPCommentsIfNecessary( file: InputFile ): StringInputFile = {
    val output = file.read
    val lines = output.split( "\n" )
    if ( lines contains "%----ERROR: Could not form TPTP format derivation" )
      StringInputFile( lines.toSeq.
        dropWhile( _ != "%----ORIGINAL SYSTEM OUTPUT" ).drop( 1 ).
        takeWhile( !_.startsWith( "%-----" ) ).dropRight( 1 ).
        map { _ substring 2 }.
        filterNot( _ startsWith "% SZS" ).
        filterNot( _ startsWith "\\n% SZS" ).
        mkString( "", "\n", "\n" ) )
    else
      StringInputFile( output )
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
