package at.logic.gapt.provers.veriT

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.formats.veriT._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansion._
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

  private def withGroundVariables2( seq: HOLSequent )( f: HOLSequent => Option[ExpansionProof] ): Option[ExpansionProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map {
      case ExpansionProof( renamedExpSeq ) =>
        ExpansionProof( renamedExpSeq map { TermReplacement( _, invertRenaming ) } )
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
  override def getExpansionProofWithCut( s: HOLSequent ): Option[ExpansionProofWithCut] = withGroundVariables2( s ) { s =>
    val ( smtBenchmark, _, renaming ) = SmtLibExporter( s )
    val output = runProcess( Seq( "veriT", "--proof=-", "--proof-version=1" ), smtBenchmark )

    VeriTParser.getExpansionProof( new StringReader( output ) ) map { renamedExpansion =>
      val undoRenaming = renaming.map {
        case ( from, to @ Const( smtName, FunctionType( TBase( "Bool" ), argTypes ) ) ) => FOLAtomConst( smtName, argTypes.size ) -> from
        case ( from, to @ Const( smtName, FunctionType( _, argTypes ) ) )               => FOLFunctionConst( smtName, argTypes.size ) -> from
      } ++ Map( FOLConst( "false" ) -> Bottom(), FOLConst( "true" ) -> Top() )
      val exp_seq = for ( et <- renamedExpansion ) yield TermReplacement( et, undoRenaming.toMap[LambdaExpression, LambdaExpression] )

      val exp_seq_quant = exp_seq filter { e => containsQuantifier( e.shallow ) }

      val prop = for ( ( f, idx ) <- s.zipWithIndex ) yield formulaToExpansionTree( f, idx.isSuc )

      val quasi_taut = exp_seq_quant ++ prop
      val taut = addSymmetry( quasi_taut )

      ExpansionProof( taut )
    }
  }

  override def getLKProof( s: HOLSequent ) = getExpansionProof( s ) map { ExpansionProofToLK( _ ) }

  def addEquationalAxioms( epwc: ExpansionProofWithCut ): Option[ExpansionProofWithCut] =
    for ( ExpansionProofWithCut( Seq(), veritExpansion ) <- getExpansionProofWithCut( epwc.deep ) ) yield {
      val equationalAxioms = veritExpansion filter { t => containsQuantifier( t.shallow ) } map { t =>
        freeVariables( t.shallow ).foldLeft( t )( ( t_, fv ) => ETWeakQuantifier( All( fv, t_.shallow ), Map( fv -> t_ ) ) )
      }
      epwc.copy( expansionSequent = equationalAxioms ++ epwc.expansionSequent )
    }

  val isInstalled: Boolean =
    try {
      runProcess( Seq( "veriT", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
