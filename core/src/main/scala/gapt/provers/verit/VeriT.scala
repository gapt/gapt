package gapt.provers.verit

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.formula.hol.containsQuantifier
import gapt.expr.formula.hol.instantiate
import gapt.expr.util.freeVariables
import gapt.formats.smt.SmtLibExporter
import gapt.formats.verit._
import gapt.logic.Polarity
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion._
import gapt.proofs.lk.LKProof
import gapt.provers._
import gapt.utils.ExternalProgram
import gapt.utils.Maybe
import gapt.utils.runProcess

import java.io._

case class FormulaInstance( formula: Formula, terms: Seq[Expr] ) {
  val instance: Formula = instantiate( formula, terms )
}

object VeriT extends VeriT
class VeriT extends OneShotProver with ExternalProgram {

  override def isValid( s: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = {

    // Generate the input file for veriT
    val veritInput = SmtLibExporter( groundFreeVariables( s )._1, lineWidth = Int.MaxValue )._1

    val veritOutput = runProcess( Seq( "veriT", "--disable-print-success", "--disable-banner" ), veritInput )

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
  override def getExpansionProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
    groundFreeVariables.wrap( s ) { inputSequent =>
      val ( smtBenchmark, _, renaming ) = SmtLibExporter( inputSequent, lineWidth = Int.MaxValue )
      val output = runProcess(
        Seq( "veriT", "--proof=-", "--disable-print-success", "--disable-banner" ), smtBenchmark )

      val undoRenaming = renaming.map {
        case ( from, to ) => to.name -> from
      } ++ Map( "false" -> Bottom(), "true" -> Top() )

      val expansionProof = VeriTParser.parseProof( output ).map { proof =>
        val equalityInstances = aletheQfUf.collectEqualityInstances( proof, undoRenaming )
        val equalityExpansionTrees = equalityInstances
          .groupBy { case FormulaInstance( f, ts ) => ( f, ts.size ) }
          .map {
            case ( ( ax, vs ), instances ) =>
              ETWeakQuantifierBlock(
                ax,
                vs,
                instances.map { i => ( i.terms, formulaToExpansionTree( i.instance, Polarity.InAntecedent ) ) } )
          }
        val inputExpansionSequent =
          inputSequent.zipWithIndex.map { case ( f, idx ) => formulaToExpansionTree( f, idx.polarity ) }
        val expansionSequentWithoutSymmetry = equalityExpansionTrees ++: inputExpansionSequent
        ExpansionProof( addSymmetry( expansionSequentWithoutSymmetry ) )
      }
      expansionProof
    }
  }

  override def getLKProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = getExpansionProof( s ) map { ep =>
    val Right( p ) = PropositionalExpansionProofToLK( ep )
    p
  }

  def addEquationalAxioms( epwc: ExpansionProof ): Option[ExpansionProof] =
    for ( ExpansionProof( veritExpansion ) <- getExpansionProof( epwc.deep ) ) yield {
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
      case _: IOException => false
    }
}
