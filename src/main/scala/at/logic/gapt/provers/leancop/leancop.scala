package at.logic.gapt.provers.leancop

import java.io.{ ByteArrayOutputStream, StringReader }

import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.sys.process._

/*

 Unfortunately, leancop cannot be installed easily--it can only be run
 in the directory where it was extracted.

 As a workaround, you need to place a script like the following in your
 PATH:

#!/bin/sh
file=$(readlink -f "$1")
cd ~/Downloads/leancop22casc14
./leancop.sh "$file"

 */

class LeanCoPProver extends Prover with ExternalProgram {

  override def isValid( s: FSequent ): Boolean =
    getExpansionSequent( s ).isDefined

  override def getExpansionSequent( s: FSequent ): Option[ExpansionSequent] = {
    val tptp = TPTPFOLExporter.tptp_proof_problem_split( s )
    val leanCopOutput = withTempFile.fromString( tptp ) { tptpFile =>
      Seq( "leancop", tptpFile ) !!
    }

    // extract the part between the %----- delimiters
    val tptpProof = leanCopOutput.split( "\n" ).
      dropWhile( !_.startsWith( "%" ) ).drop( 1 ).
      takeWhile( !_.startsWith( "%" ) ).
      mkString( "\n" )

    LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) )
  }

  override def getLKProof( seq: FSequent ): Option[LKProof] =
    throw new UnsupportedOperationException

  override val isInstalled: Boolean = ( Seq( "which", "leancop" ) #> new ByteArrayOutputStream ! ) == 0
}