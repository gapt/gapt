package at.logic.gapt.provers.leancop

import java.io.{ IOException, ByteArrayOutputStream, StringReader }

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.{ OneShotProver, renameConstantsToFi, Prover }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.{ runProcess, withTempFile }

object LeanCoP extends LeanCoP
class LeanCoP extends OneShotProver with ExternalProgram {
  val nLine = sys.props( "line.separator" )

  override def isValid( s: HOLSequent ): Boolean =
    getExpansionSequent( s ).isDefined

  override def getExpansionSequent( s: HOLSequent ): Option[ExpansionSequent] =
    withRenamedConstants( s ) { seq =>
      require( seq.succedent.size == 1 )

      val tptp = TPTPFOLExporter.tptp_proof_problem_split( seq )
      val leanCopOutput = runProcess.withTempInputFile( Seq( "leancop" ), tptp )

      // extract the part between the %----- delimiters
      val tptpProof = leanCopOutput.split( nLine ).
        dropWhile( !_.startsWith( "%-" ) ).drop( 1 ).
        takeWhile( !_.startsWith( "%-" ) ).
        mkString( nLine )

      LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) )
    }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    throw new UnsupportedOperationException

  override val isInstalled: Boolean = try runProcess.withExitValue( Seq( "leancop" ) )._1 == 2
  catch { case _: IOException => false }

  private def withRenamedConstants( seq: HOLSequent )( f: HOLSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, _, invertRenaming ) = renameConstantsToFi( seq )
    f( renamedSeq ) map { renamedExpSeq =>
      renamedExpSeq map { TermReplacement( _, invertRenaming toMap ) }
    }
  }
}
