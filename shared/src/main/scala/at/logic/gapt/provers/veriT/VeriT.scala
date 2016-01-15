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
class VeriT extends OneShotProver with ExternalProgram {

  override def isValid( s: HOLSequent ): Boolean = {

    // Generate the input file for veriT
    val veritInput = SmtLibExporter( groundFreeVariables( s )._1 )._1

    val veritOutput = runProcess( Seq( "veriT" ), veritInput )

    // Parse the output
    VeriTParser.isUnsat( new StringReader( veritOutput ) )
  }

  private def withGroundVariables2( seq: HOLSequent )( f: HOLSequent => Option[ExpansionSequent] ): Option[ExpansionSequent] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      renamedProof map { TermReplacement( _, invertRenaming ) }
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
  override def getExpansionSequent( s: HOLSequent ): Option[ExpansionSequent] = withGroundVariables2( s ) { s =>
    val ( smtBenchmark, _, renaming ) = SmtLibExporter( s )
    val output = runProcess( Seq( "veriT", "--proof=-", "--proof-version=1" ), smtBenchmark )

    VeriTParser.getExpansionProof( new StringReader( output ) ) map { renamedExpansion =>
      val undoRenaming: Map[LambdaExpression, LambdaExpression] = renaming map {
        case ( from, to @ Const( smtName, FunctionType( TBase( "Bool" ), argTypes ) ) ) => FOLAtomConst( smtName, argTypes.size ) -> from
        case ( from, to @ Const( smtName, FunctionType( _, argTypes ) ) )               => FOLFunctionConst( smtName, argTypes.size ) -> from
      }
      val exp_seq = for ( et <- renamedExpansion ) yield TermReplacement( et, undoRenaming )

      val exp_seq_quant = exp_seq filter { isQuantified( _ ) }

      val prop = for ( ( f, idx ) <- s.zipWithIndex ) yield formulaToExpansionTree( f, idx.isSuc )

      val quasi_taut = exp_seq_quant ++ prop
      val taut = addSymmetry( quasi_taut )

      taut
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
