/* Rewriting on Formulas on Sequent Calculus Proofs */

package at.logic.gapt.proofs.lk.algorithms

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.language.hol._
import at.logic.gapt.proofs.lk.base.{ FSequent, LKProof, Sequent }
import at.logic.gapt.proofs.occurrences.{ FormulaOccurrence, defaultFormulaOccurrenceFactory }

object Util {
  class ElimEx( val uproofs: List[LKProof], val aux: List[FormulaOccurrence], val prim: HOLFormula, val defs: Option[Map[FormulaOccurrence, FormulaOccurrence]] ) extends Exception {
    override def getMessage = {
      var s = "proofs:\n\n"
      for ( p <- uproofs )
        s = s + p.toString() + "\n"
      s = s + "\nauxiliary formulas:\n\n"
      for ( p <- aux )
        s = s + p.toString() + "\n"
      s = s + "\nprimary formula:\n" + prim + "\n"

      s
    }
  }

  //debugging stuff
  def print_hashcodes( msg: String, s: Sequent ) = {
    println( msg )
    println( s )
    print( s.antecedent map ( ( x: FormulaOccurrence ) => x.id ) )
    print( " :- " )
    print( s.succedent map ( ( x: FormulaOccurrence ) => x.id ) )
    println()
  }

  def print_hashcodes( msg: String, m: Map[FormulaOccurrence, FormulaOccurrence] ) = {
    println( msg )
    println( m )
    println( m map ( ( x: ( FormulaOccurrence, FormulaOccurrence ) ) => ( x._1.id, x._2.id ) ) )
  }

  def check_map( map: Map[FormulaOccurrence, FormulaOccurrence], proof: LKProof ): Boolean = {
    val ant = proof.root.antecedent
    val succ = proof.root.succedent
    for ( el <- map.values ) {
      println( "searching for " + System.identityHashCode( el ) )
      if ( ( !ant.contains( el ) ) && ( !succ.contains( el ) ) )
        throw new ElimEx( proof :: Nil, el :: Nil, el.formula, Some( map ) )
    }
    true
  }

  def check_map( map: Map[FormulaOccurrence, FormulaOccurrence], proof: LKProof, dproof: LKProof ): Boolean =
    check_map( map, proof.root, dproof.root )

  def check_map( map: Map[FormulaOccurrence, FormulaOccurrence], root: Sequent, droot: Sequent ): Boolean = {
    var error = false
    for ( fo <- root.antecedent ) {
      if ( !( map.keySet contains fo ) ) {
        println( "PROBLEM: map does not contain " + fo.id )
        error = true
      } else if ( !( droot.antecedent contains map( fo ) ) ) {
        println( "PROBLEM: FO #" + fo.id, " maps to " + map( fo ).id + ", but is not present in antecedent of new root!" )
        error = true
      }
    }
    for ( fo <- root.succedent ) {
      if ( !( map.keySet contains fo ) ) {
        println( "PROBLEM: map does not contain " + fo.id )
        error = true
      } else if ( !( droot.succedent contains map( fo ) ) ) {
        println( "PROBLEM: FO #" + fo.id, " maps to " + map( fo ).id + ", but is not present in succedent of new root!" )
        error = true
      }
    }

    if ( error ) {
      print_hashcodes( "Original Proof:", root )
      print_hashcodes( "Modified Proof:", droot )
      print_hashcodes( "Map:", map )
    }

    error
  }
  //fsequent2sequent
  def f2focc( f: HOLFormula ) = new FormulaOccurrence( f, Nil, defaultFormulaOccurrenceFactory )
  def fsequent2sequent( s: FSequent ) = Sequent( s._1 map f2focc, s._2 map f2focc )

}

