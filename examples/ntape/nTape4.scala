package at.logic.gapt.examples

import at.logic.gapt.expr.{ Ti, Var, Eq }
import at.logic.gapt.formats.llkNew.loadLLK
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.lkOld.{ deleteTautologies, subsumedClausesRemoval }
import at.logic.gapt.proofs.lkskNew.LKskProof

/**
 * Version 3 of the higher-order n-Tape proof.
 */
case class nTape4( size: Int ) extends nTape {
  require( 1 < size && size < 5, "We have only instances 2 to 4." )

  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream s"ntape/ntape4-$size.llk" )

  override def root_proof() = "TAPEPROOF"

  override lazy val preprocessed_css: List[HOLSequent] = {
    val stripped_css = css.map( _.map( LKskProof.getFormula ) )
    val equality = Sequent( Nil, List( Eq( Var( "x", Ti ), Var( "x", Ti ) ) ) )
    subsumedClausesRemoval( equality :: deleteTautologies( stripped_css ).toList )
  }

  //prints the interesting terms from the expansion sequent
  override def printStatistics() = {
    println( "------------ Proof sizes --------------" )
    println( s"Input proof            : ${input_proof.treeLike.size}" )
    println( s"Preprocessed input     : ${preprocessed_input_proof.treeLike.size}" )
    println( s"LKsk input proof       : ${lksk_proof.treeLike.size}" )
    println( s"ACNF output proof      : (not available)" )
    println( "------------ " )
    println( s"Css size               : ${css.size}" )
    println( s"Preprocessed css size  : ${preprocessed_css.size}" )
    println( "------------ " )
    println( s"Refutation size (dag)  : (not available)" )
    println( s"Refutation size (tree) : (not available)" )
    println( s"Refutation depth       : (not available)" )
    println( "------------ " )
    println( s"Reproved deep formula proof size (dag)  : (not available)" )
    println( s"Reproved deep formula proof size (tree) : (not available)" )
  }
}
