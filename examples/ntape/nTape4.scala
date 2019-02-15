package gapt.examples

import gapt.expr.formula.hol.freeHOVariables
import gapt.expr.ty.Ti
import gapt.expr.Var
import gapt.expr.formula.Eq
import gapt.formats.ClasspathInputFile
import gapt.formats.llk.loadLLK
import gapt.proofs.ceres.{ deleteTautologies, subsumedClausesRemoval }
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.proofs.ceres_omega.AnalysisWithCeresOmega

/**
 * Version 3 of the higher-order n-Tape proof.
 */
class nTape4( val size: Int ) extends AnalysisWithCeresOmega {
  require( 1 < size && size < 5, "We have only instances 2 to 4." )

  override def proofdb() = loadLLK( ClasspathInputFile( s"ntape/ntape4-$size.llk" ) )

  override def root_proof() = "TAPEPROOF"

  override lazy val preprocessed_css: List[HOLSequent] = {
    val stripped_css = css
    val equality = Sequent( Nil, List( Eq( Var( "x", Ti ), Var( "x", Ti ) ) ) )
    subsumedClausesRemoval( equality :: deleteTautologies( stripped_css ).toList )
  }

  lazy val preprocessed_css_hol_clauses =
    preprocessed_css.filter( _.filter( freeHOVariables( _ ).nonEmpty ).nonEmpty )

  //prints the interesting terms from the expansion sequent
  override def printStatistics() = {
    println( "------------ Proof sizes --------------" )
    println( s"Input proof              : ${input_proof.treeLike.size}" )
    println( s"Preprocessed input       : ${preprocessed_input_proof.treeLike.size}" )
    println( s"LKsk input proof         : ${lksk_proof.treeLike.size}" )
    println( s"ACNF output proof        : (not available)" )
    println( "------------ " )
    println( s"Css size                 : ${css.size}" )
    println( s"Preprocessed css size    : ${preprocessed_css.size}" )
    println( s"Clauses with HOL content : ${preprocessed_css_hol_clauses.size}" )
    println( "------------ " )
    println( s"Refutation size (dag)    : (not available)" )
    println( s"Refutation size (tree)   : (not available)" )
    println( s"Refutation depth         : (not available)" )
    println( "------------ " )
    println( s"Reproved deep formula proof size (dag)  : (not available)" )
    println( s"Reproved deep formula proof size (tree) : (not available)" )
  }
}

object nTape4 {
  lazy val inst2 = new nTape4( 2 )
  lazy val inst3 = new nTape4( 3 )
  lazy val inst4 = new nTape4( 4 )

  def apply( size: Int ) = size match {
    case 2 => inst2
    case 3 => inst3
    case 4 => inst4
    case _ => throw new Exception( "We have only instances 2 to 4." )
  }
}