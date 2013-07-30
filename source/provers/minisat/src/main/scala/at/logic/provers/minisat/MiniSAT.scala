/**
 * Interface to the MiniSAT solver.
 * Needs the command-line tool minisat to work.
 */

package at.logic.provers.minisat

import at.logic.language.hol._
import at.logic.calculi.resolution.base._
import at.logic.algorithms.resolution.CNFp
  
import java.io.BufferedReader
import java.io.BufferedWriter
import java.io.File
import java.io.FileInputStream
import java.io.FileWriter
import java.io.InputStreamReader
import java.lang.StringBuilder

import scala.collection.immutable.HashMap

trait Interpretation {
  // Interpret an atom.
  def interpretAtom(atom : HOLFormula) : Boolean
  
  // Interpret an arbitrary formula.
  def interpret(f : HOLFormula) : Boolean = f match {
    case And(f1, f2) => interpret(f1) && interpret(f2)
    case Or(f1, f2) => interpret(f1) || interpret(f2)
    case Imp(f1, f2) => !interpret(f1) || interpret(f2)
    case Neg(f1) => !interpret(f1)
    case Atom(_, _) => interpretAtom(f)
  }
    
}

// Call MiniSAT to solve quantifier-free HOLFormulas.
class MiniSAT {
  
  class MapBasedInterpretation( val model : Map[HOLFormula, Boolean]) extends Interpretation {
    def interpretAtom(atom : HOLFormula) = model.get(atom) match {
      case Some(b) => b
      case None => false
    }
  }

  var atom_map : Map[HOLFormula, Int] = new HashMap[HOLFormula,Int]
  
  // Checks if f is valid using MiniSAT.
  def isValid( f: HOLFormula ) = solve( Neg( f ) ) match {
    case Some(_) => false
    case None => true
  }
  
  // Returns a model of the formula obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( f: HOLFormula ) : Option[Interpretation] = solve( CNFp(f) )
  
  // Returns a model of the set of clauses obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( problem: Set[FClause] ) : Option[Interpretation] =
    getFromMiniSAT(problem) match {
      case Some(model) => Some(new MapBasedInterpretation(model))
      case None => None
    }

  private def updateAtoms( clauses : Set[FClause] ) =
  {
    // FIXME: cast :-(
    val atoms = clauses.flatMap( c => c.neg.asInstanceOf[Seq[HOLFormula]] ++ c.pos.asInstanceOf[Seq[HOLFormula]] );
    atom_map = atoms.zip(1 to atoms.size).toMap
  }
  
  private def getAtom( i : Int ) = {
    atom_map.find( p => i == p._2 ) match {
      case Some((a, n)) => Some(a)
      case _ => None
    }
  }

  private def getMiniSATString(atom: HOLFormula, pos : Boolean) : String =
    if (pos) atom_map.get(atom).get.toString else "-" + atom_map.get(atom).get
  
  private def getMiniSATString(clause : FClause) : String =
  {
    val sb = new StringBuilder()

    def atoms_to_str( as : Seq[HOLFormula], pol : Boolean ) = as.foreach( a => {
      sb.append(getMiniSATString(a, pol));
      sb.append(" ");
    } )
    
    
    // FIXME: cast :-(
    atoms_to_str( clause.pos.asInstanceOf[Seq[HOLFormula]], true )
    atoms_to_str( clause.neg.asInstanceOf[Seq[HOLFormula]], false )

    sb.toString()
  }
  
  private def getFromMiniSAT( clauses : Set[FClause] ) :  Option[Map[HOLFormula, Boolean]] =
  {
    updateAtoms(clauses)
    val sb = new StringBuilder()
    
    val nl = System.getProperty("line.separator")
    
    sb.append("p cnf " + atom_map.size + " "  + clauses.size + nl)

    // construct minisat text input
    clauses.foreach ( c => 
    {
      sb.append(getMiniSATString(c))
      sb.append(" 0")
      sb.append(nl)
    } )
    
    val temp_in = File.createTempFile("agito_minisat_in",".sat")
    temp_in.deleteOnExit()
        
    val temp_out = File.createTempFile("agito_minisat_out",".sat")
    temp_out.deleteOnExit()
    
    val out = new BufferedWriter(new FileWriter(temp_in))
    out.append(sb.toString())
    out.close()
    
    //System.out.println(sb.toString());
    
    // run minisat
    
    val bin = "minisat";
    val run = bin + " " + temp_in.getAbsolutePath() + " " + temp_out.getAbsolutePath();
    //System.out.println("Starting minisat...");
    val p = Runtime.getRuntime().exec(run);
    p.waitFor();
    //System.out.println("minisat finished.");
    
    // parse minisat output and construct map
    val in = new BufferedReader(new InputStreamReader(
            new FileInputStream(temp_out)));
    
    val sat = in.readLine();
    
    //System.out.println(sat);
    
    if ( sat.equals("SAT") ) {
      Some( in.readLine().split(" ").
           filter(lit => !lit.equals("") && !lit.charAt(0).equals('0')).
           map( lit => 
             if (lit.charAt(0) == '-') {
               // negative literal
               (getAtom(lit.substring(1).toInt).get, false)
             } else {
               // positive literal
               (getAtom(lit.toInt).get, true)
             })
        .toSet.toMap)
    } else {
      // unsatisfiable
      None
    }
  }
}
