package gapt.examples

import gapt.examples.Script
import gapt.proofs.ceres.StructCreators
import gapt.proofs.lk.{ AtomicExpansion, regularize }
import java.nio.file.{ Paths, Files }

import gapt.expr.hol._

import gapt.formats.latex.SequentsListLatexExporter

import gapt.formats.tptp.TptpHOLExporter
import gapt.proofs.HOLSequent

/* *************************************************************************** *
   n-Tape Proof script: loads an instance of the n-Tape proof, extracts the
   characteristic sequent set and exports it to tptp.
 * *************************************************************************** */
/*
object inst extends Script {
  /* adjust filename to load a different example */
  //val filename = "tape3-4c.llk"
  val filename = "examples/ntape/tape3-3.llk"

  /* begin of proof script  */

  object exportLatex {
    def apply( list: List[HOLSequent], fn: String ) = {
      val writer = new FileWriter( fn ) with SequentsListLatexExporter with HOLTermArithmeticalExporter
      writer.exportSequentList( list, Nil ).close
    }
  }

  object exportTHF {
    def apply( ls: List[HOLSequent], filename: String, positive: Boolean = false ) =
      Files.write( Paths.get( filename ), TPTPHOLExporter( ls, positive ).getBytes )
  }

  private val nLine = sys.props( "line.separator" )

  def show( s: String ) = println( nLine + nLine + "+++++++++ " + s + " ++++++++++" + nLine )

  show( "Loading file" )
  val pdb = HybridLatexParser( filename )

  show( "Eliminating definitions, expanding tautological axioms" )
  val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions )( regularize( pdb.proof( "TAPEPROOF" ) ) ) )

  show( "Skolemizing" )
  val selp = LKToLKsk( elp )

  show( "Extracting struct" )
  val struct = StructCreators.extract( selp, x => containsQuantifierOnLogicalLevel( x ) || freeHOVariables( x ).nonEmpty )

  show( "Computing clause set" )
  //val cl = AlternativeStandardClauseSet(struct)
  val cl = SimpleStandardClauseSet( struct )
  //val cl = StandardClauseSet.transformStructToClauseSet(struct).map(_.toHOLSequent)

  show( "simplifying clause set" )
  val fs = HOLSequent( Nil, List( HLKHOLParser.parseFormula( "var x :i; x = x" ) ) )
  val rcl = subsumedClausesRemovalHOL( fs :: ( cl.toList ) )
  val tcl = deleteTautologies( rcl )

  show( "exporting to THF and Tex" )
  exportTHF( tcl.sorted( HOLSequentOrdering ), filename + ".tptp" )
  exportLatex( tcl.sorted( HOLSequentOrdering ), filename + ".tex" )

  show( "statistics" )
  println( "Clause set:" + cl.size )
  println( "Reduced clause set:" + tcl.size )
}
*/
