package at.logic.gapt.provers.veriT

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.formats.veriT._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.runProcess
import java.io._
import at.logic.gapt.provers._
import at.logic.gapt.expr._

object VeriT extends VeriT
class VeriT extends Prover with ExternalProgram {

  override def isValid( s: HOLSequent ): Boolean = {

    // Generate the input file for veriT
    val veritInput = SmtLibExporter( renameConstantsToFi( s )._1 )

    val veritOutput = runProcess( Seq( "veriT" ), veritInput )

    // Parse the output
    VeriTParser.isUnsat( new StringReader( veritOutput ) )
  }

  private def withRenamedConstants( seq: HOLSequent )( f: HOLSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, _, invertRenaming ) = renameConstantsToFi( seq )
    f( renamedSeq ) map { renamedExpSeq =>
      renamedExpSeq map { TermReplacement( _, invertRenaming.toMap[LambdaExpression, LambdaExpression] ) }
    }
  }

  /*
   * Given a sequent A1, ..., An |- B1, ..., Bm, veriT's proof is actually of
   * the sequent A1, ..., An, not B1, ..., not Bm |-.
   * Currently there is no way to recover the antecedent/succedent formulas from
   * veriT's output, so in this method we re-build the expansion sequent by
   * taking the quantified equality axioms from the proof returned by veriT and
   * merging them with the original end-sequent.
   */
  override def getExpansionSequent( s: HOLSequent ): Option[ExpansionSequent] = withRenamedConstants( s ) { s =>
    val smtBenchmark = SmtLibExporter( s )

    val output = runProcess( Seq( "veriT", "--proof=-", "--proof-version=1" ), smtBenchmark )

    VeriTParser.getExpansionProof( new StringReader( output ) ) match {
      case Some( exp_seq ) =>
        val exp_seq_quant = new ExpansionSequent(
          exp_seq.antecedent.filter( f => isQuantified( f ) ),
          exp_seq.succedent.filter( f => isQuantified( f ) )
        )

        val ant_prop = s.antecedent.map( f => formulaToExpansionTree( f, false ) )
        val suc_prop = s.succedent.map( f => formulaToExpansionTree( f, true ) )

        val quasi_taut = new ExpansionSequent( exp_seq_quant.antecedent ++ ant_prop, exp_seq_quant.succedent ++ suc_prop )
        val taut = addSymmetry( quasi_taut )

        Some( taut )

      case None => None
    }
  }

  override def getLKProof( s: HOLSequent ) = getExpansionSequent( s ) map { ExpansionProofToLK( _ ) }

  val isInstalled: Boolean =
    try {
      runProcess( Seq( "veriT", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
