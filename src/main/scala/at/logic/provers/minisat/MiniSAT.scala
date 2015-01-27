/**
 * Interface to the MiniSAT solver.
 * Needs the command-line tool minisat to work.
 */

package at.logic.provers.minisat

import at.logic.language.fol.FOLFormula
import at.logic.language.hol._
import at.logic.calculi.resolution._
import at.logic.algorithms.resolution.{CNFp, TseitinCNF}
  
import java.io._
import java.lang.StringBuilder

import at.logic.calculi.lk.base.FSequent

import at.logic.provers.Prover

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
class MiniSAT extends at.logic.utils.logging.Stopwatch {

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
  def solve( f: HOLFormula ) : Option[Interpretation] = {
    start()
    val cnf = f match {
      case f1: FOLFormula => TseitinCNF(f1)._1
      case _              => CNFp(f)
    }
    lap("CNF done")
    val int = solve( cnf )
    lap("Solving done")
    int
  }
  
  // Returns a model of the set of clauses obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( problem: List[FClause] ) : Option[Interpretation] =
    getFromMiniSAT(problem) match {
      case Some(model) => Some(new MapBasedInterpretation(model))
      case None => None
    }

  private def updateAtoms( clauses : List[FClause] ) =
  {
    val atoms = clauses.flatMap( c => c.neg ++ c.pos ).distinct;
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
    
    atoms_to_str( clause.pos, true )
    atoms_to_str( clause.neg, false )

    sb.toString()
  }
  
  private def getFromMiniSAT( clauses : List[FClause] ) :  Option[Map[HOLFormula, Boolean]] =
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
    
    trace( "Generated MiniSAT input: ")
    trace(sb.toString());
    
    // run minisat
    
    val bin = "minisat";
    val run = bin + " " + temp_in.getAbsolutePath() + " " + temp_out.getAbsolutePath();
    debug("Starting minisat...");
    val p = Runtime.getRuntime().exec(run);
    p.waitFor();
    debug("minisat finished.");
    
    // parse minisat output and construct map
    val in = new BufferedReader(new InputStreamReader(
            new FileInputStream(temp_out)));
    
    val sat = in.readLine();
    
    trace("MiniSAT result: " + sat)
    
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

class MiniSATProver extends Prover with at.logic.utils.logging.Logger with at.logic.utils.traits.ExternalProgram {
  def getLKProof( seq : FSequent ) : Option[at.logic.calculi.lk.base.LKProof] = 
    throw new Exception("MiniSAT does not produce proofs!")

  override def isValid( f : HOLFormula ) : Boolean = {
    val sat = new MiniSAT()
    sat.isValid(f)
  }

  override def isValid( seq : FSequent ) : Boolean = {
    val sat = new MiniSAT()
    trace("calling MiniSAT.isValid( " + Imp(And(seq.antecedent.toList), Or(seq.succedent.toList)) + ")")
    sat.isValid(Imp(And(seq.antecedent.toList), Or(seq.succedent.toList)))
  }

  def isInstalled(): Boolean =
    try {
      val box : List[FClause] = List()
      (new MiniSAT).solve(box)
      true
    } catch  {
      case ex: IOException => false
    }

}
