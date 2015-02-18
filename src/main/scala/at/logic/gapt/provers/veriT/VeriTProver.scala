
package at.logic.gapt.provers.veriT

import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import scala.sys.process._
import java.io._
import at.logic.gapt.provers.Prover
import at.logic.gapt.io.veriT._
import at.logic.gapt.language.hol.HOLFormula
import at.logic.gapt.proofs.lk.base.FSequent

class VeriTProver extends Prover with at.logic.gapt.utils.traits.ExternalProgram {

  override def isValid( s: FSequent ): Boolean = {

    // Generate the input file for veriT
    val veritInput = VeriTExporter( s )

    val veritOutput = "veriT" #< new ByteArrayInputStream( veritInput.getBytes ) !!

    // Parse the output
    VeriTParser.isUnsat( new StringReader( veritOutput ) )
  }

  def getExpansionSequent( s: FSequent ): Option[ExpansionSequent] = {
    val smtBenchmark = VeriTExporter( s )

    val output = "veriT --proof=- --proof-version=1" #< new ByteArrayInputStream( smtBenchmark.getBytes ) !!

    VeriTParser.getExpansionProof( new StringReader( output ) )
  }

  // VeriT proofs are parsed as Expansion Trees.
  // At the moment there is no method implemented that 
  // would generate an LK proof from an Expansion Tree.
  override def getLKProof( s: FSequent ) =
    throw new Exception( "It is not possible to generate LK proofs from VeriT proofs at the moment." )
  override def getLKProof( f: HOLFormula ) =
    throw new Exception( "It is not possible to generate LK proofs from VeriT proofs at the moment." )

  def isInstalled(): Boolean =
    try {
      "veriT --disable-banner".!!
      true
    } catch {
      case ex: IOException => false
    }
}
