package at.logic.gapt.provers.veriT

import at.logic.gapt.formats.veriT._
import at.logic.gapt.proofs.expansionTrees.{ ExpansionSequent, isQuantified, formulaToExpansionTree }
import at.logic.gapt.utils.traits.ExternalProgram
import scala.sys.process._
import java.io._
import at.logic.gapt.provers._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.base.FSequent

class VeriTProver extends Prover with ExternalProgram {

  override def isValid( s: FSequent ): Boolean = {

    // Generate the input file for veriT
    val veritInput = VeriTExporter( s )

    val veritOutput = "veriT" #< new ByteArrayInputStream( veritInput.getBytes ) !!

    // Parse the output
    VeriTParser.isUnsat( new StringReader( veritOutput ) )
  }

  /*
   * Given a sequent A1, ..., An |- B1, ..., Bm, veriT's proof is actually of
   * the sequent A1, ..., An, not B1, ..., not Bm |-.
   * Currently there is no way to recover the antecedent/succedent formulas from
   * veriT's output, so in this method we re-build the expansion sequent by
   * taking the quantified equality axioms from the proof returned by veriT and
   * merging them with the original end-sequent.
   */
  def getExpansionSequent( s: FSequent ): Option[ExpansionSequent] = {
    val smtBenchmark = VeriTExporter( s )

    val output = "veriT --proof=- --proof-version=1" #< new ByteArrayInputStream( smtBenchmark.getBytes ) !!

    VeriTParser.getExpansionProof( new StringReader( output ) ) match {
      case Some( exp_seq ) =>
        val exp_seq_quant = new ExpansionSequent(
          exp_seq.antecedent.filter( f => isQuantified( f ) ),
          exp_seq.succedent.filter( f => isQuantified( f ) ) )

        val ant_prop = s.antecedent.map( f => formulaToExpansionTree( f, false ) )
        val suc_prop = s.succedent.map( f => formulaToExpansionTree( f, true ) )

        Some( new ExpansionSequent( exp_seq_quant.antecedent ++ ant_prop, exp_seq_quant.succedent ++ suc_prop ) )

      case None => None
    }
  }

  // VeriT proofs are parsed as Expansion Trees.
  // At the moment there is no method implemented that 
  // would generate an LK proof from an Expansion Tree.
  override def getLKProof( s: FSequent ) =
    throw new Exception( "It is not possible to generate LK proofs from VeriT proofs at the moment." )
  override def getLKProof( f: HOLFormula ) =
    throw new Exception( "It is not possible to generate LK proofs from VeriT proofs at the moment." )

  val isInstalled: Boolean =
    try {
      "veriT --disable-banner".!!
      true
    } catch {
      case ex: IOException => false
    }
}
