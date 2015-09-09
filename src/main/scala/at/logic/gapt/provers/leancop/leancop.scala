package at.logic.gapt.provers.leancop

import java.io.{ ByteArrayOutputStream, StringReader }

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.algorithms.rewriting.NameReplacement.SymbolMap
import at.logic.gapt.expr.{ Const, FOLHeadType, constants }
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.provers.renameConstantsToFi
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.sys.process._

class LeanCoPProver extends Prover with ExternalProgram {
  val nLine = sys.props( "line.separator" )

  override def isValid( s: HOLSequent ): Boolean =
    getExpansionSequent( s ).isDefined

  override def getExpansionSequent( s: HOLSequent ): Option[ExpansionSequent] =
    withRenamedConstants( s ) { seq =>
      require( seq.succedent.size == 1 )

      val tptp = TPTPFOLExporter.tptp_proof_problem_split( seq )
      val leanCopOutput = withTempFile.fromString( tptp ) { tptpFile =>
        Seq( "leancop", tptpFile ) !!
      }

      // extract the part between the %----- delimiters
      val tptpProof = leanCopOutput.split( nLine ).
        dropWhile( !_.startsWith( "%-" ) ).drop( 1 ).
        takeWhile( !_.startsWith( "%-" ) ).
        mkString( nLine )

      LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) )
    }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    throw new UnsupportedOperationException

  override val isInstalled: Boolean = ( Seq( "which", "leancop" ) #> new ByteArrayOutputStream ! ) == 0

  private def withRenamedConstants( seq: HOLSequent )( f: HOLSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, _, invertRenaming ) = renameConstantsToFi( seq )
    f( renamedSeq ) map { renamedExpSeq =>
      NameReplacement( renamedExpSeq, invertRenaming )
    }
  }
}
