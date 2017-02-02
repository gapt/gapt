package at.logic.gapt.proofs

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.formats.leancop.LeanCoPParser
import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.formats.verit.VeriTParser
import at.logic.gapt.proofs.expansion.{ ExpansionProof, addSymmetry }
import at.logic.gapt.proofs.resolution.{ ResolutionProof, ResolutionToExpansionProof, containsEquationalReasoning, numberOfLogicalInferencesRes, simplifyResolutionProof }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.metrics
import ammonite.ops._

object loadExpansionProof {

  def apply( file: InputFile ): ExpansionProof = withBackgroundTheory( file )._1

  def withBackgroundTheory( file: InputFile ): ( ExpansionProof, CutIntroduction.BackgroundTheory ) = file.fileName match {
    case fileName if fileName endsWith ".proof_flat" =>
      val Some( expSeq ) = VeriTParser.getExpansionProofWithSymmetry( FilePath( fileName ) )
      ExpansionProof( expSeq ) -> CutIntroduction.BackgroundTheory.PureFOL
    case fileName if fileName contains "/leanCoP" =>
      val Some( expSeq ) = LeanCoPParser.getExpansionProof( extractFromTSTPCommentsIfNecessary( file ) )
      val p = ExpansionProof( expSeq )
      p -> CutIntroduction.BackgroundTheory.guess( p.shallow )
    case fileName if fileName contains "/Prover9" =>
      val ( resProof, endSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequent( file )
      loadResolutionProof( resProof, endSequent )
    case _ => // try tstp format
      val tstpOutput = file.read

      metrics.value( "tstp_is_cnf_ref", tstpOutput contains "CNFRefutation" )

      val ( endSequent, sketch ) = TptpProofParser.parse( StringInputFile( tstpOutput ), ignoreStrongQuants = true )
      metrics.value( "tstp_sketch_size", sketch.subProofs.size )

      val Right( resProof ) = RefutationSketchToResolution( sketch )
      loadResolutionProof( resProof, endSequent )
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
