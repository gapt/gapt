/**
 * Created by spoerk on 6/23/14.
 */
package at.logic.provers.qmaxsat

import at.logic.language.fol._
import scala.collection.immutable.HashMap
import scala.Some
import at.logic.calculi.resolution._
import at.logic.algorithms.resolution.CNFp
import java.io._
import scala.sys.process.{ProcessIO, Process}
import java.lang.RuntimeException

// This is also occuring in the minisat package
// TODO: eventual refactoring
trait Interpretation {
  // Interpret an atom.
  def interpretAtom(atom : FOLFormula) : Boolean

  // Interpret an arbitrary formula.
  def interpret(f : FOLFormula) : Boolean = f match {
    case And(f1, f2) => interpret(f1) && interpret(f2)
    case Or(f1, f2) => interpret(f1) || interpret(f2)
    case Imp(f1, f2) => !interpret(f1) || interpret(f2)
    case Neg(f1) => !interpret(f1)
    case Atom(_, _) => interpretAtom(f)
  }

}

/*
 * Remark: input format of wcnf
 * Weigthed Partial Max-SAT input format
 *
 *   In Weighted Partial Max-SAT, the parameters line is "p wcnf nbvar nbclauses top". We associate a weight with each clause, which is the first integer in the clause.
 *   Weights must be greater than or equal to 1, and the sum of all soft clauses smaller than 2^63.
 *   Hard clauses have weight top and soft clauses have a weight smaller than top. We assure that top is a weight always greater than the sum of the weights of violated soft clauses.
 *
 *   Example of Weighted Partial Max-SAT formula:
 *
 *   c
 *   c comments Weighted Partial Max-SAT
 *   c
 *   p wcnf 4 5 16
 *   16 1 -2 4 0
 *   16 -1 -2 3 0
 *   8 -2 -4 0
 *   4 -3 2 0
 *   3 1 3 0
 */


class MapBasedInterpretation( val model : Map[FOLFormula, Boolean]) extends Interpretation {
  def interpretAtom(atom : FOLFormula) = model.get(atom) match {
    case Some(b) => b
    case None => false
  }
}

// Call QMaxSAT to solve partial weighted MaxSAT instances
class QMaxSAT extends at.logic.utils.logging.Logger {

  val bin = "qmaxsat"

  def isInstalled() : Boolean = {
    if(new java.io.File(bin).exists())
    {
      return true
    }
    warn("It seems that QMaxSAT is not installed properly")
    warn("Please put the qmaxsat binary (available at https://sites.google.com/site/qmaxsat/) into PATH")
    return false
  }

  var atom_map : Map[FOLFormula, Int] = new HashMap[FOLFormula,Int]

  // Returns a model of a partial weighted MaxSAT instance, where
  // hard are the hard constraints and
  // soft are the soft constraints with weights w,
  // obtained from the QMaxSAT solver.
  // Returns None if unsatisfiable.
  def solvePWM( hard: Set[FOLFormula], soft: Set[Tuple2[FOLFormula, Int]] ) : Option[Interpretation] = {
    val hardCNF = hard.foldLeft(Set[FClause]())((acc,f) => acc ++ CNFp(f))
    val softCNFs = soft.foldLeft(Set[Tuple2[FClause,Int]]())((acc,s) => acc ++ CNFp(s._1).foldLeft(Set[Tuple2[FClause,Int]]())((acc,f) => acc + Tuple2[FClause,Int](f, s._2) ))
    trace("produced hard cnf: " + hardCNF)
    trace("produced soft cnf: " + softCNFs)
    solve( hardCNF, softCNFs )
  }

  // Returns a model of the set of clauses obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( hardCNF: Set[FClause], softCNFs: Set[Tuple2[FClause,Int]] ) : Option[Interpretation] =
    getFromQMaxSat(hardCNF, softCNFs) match {
      case Some(model) => Some(new MapBasedInterpretation(model))
      case None => None
    }

  private def updateAtoms( clauses : Set[FClause] ) =
  {
    val atoms = clauses.flatMap( c => c.neg.asInstanceOf[Seq[FOLFormula]] ++ c.pos.asInstanceOf[Seq[FOLFormula]] );
    atom_map = atoms.zip(1 to atoms.size).toMap
  }

  private def getAtom( i : Int ) = {
    atom_map.find( p => i == p._2 ) match {
      case Some((a, n)) => Some(a)
      case _ => None
    }
  }

  private def getQMaxSATString(atom: FOLFormula, pos : Boolean) : String =
    if (pos) atom_map.get(atom).get.toString else "-" + atom_map.get(atom).get

  private def getQMaxSATString(clause : FClause, weight: Int) : String =
  {
    val sb = new StringBuilder()

    sb.append(weight + " ")
    def atoms_to_str( as : Seq[FOLFormula], pol : Boolean ) = as.foreach( a => {
      sb.append(getQMaxSATString(a, pol));
      sb.append(" ");
    } )

    atoms_to_str( clause.pos.asInstanceOf[Seq[FOLFormula]], true )
    atoms_to_str( clause.neg.asInstanceOf[Seq[FOLFormula]], false )

    sb.toString()
  }

  object TextFileSlurper {
    def apply(file: File) : String = {
      val fileLines =
        try scala.io.Source.fromFile(file, "UTF-8").mkString catch {
          case e: java.io.FileNotFoundException => e.getLocalizedMessage()
        }
      fileLines
    }
  }

  private def getFromQMaxSat( hard: Set[FClause], soft: Set[Tuple2[FClause,Int]] ) :  Option[Map[FOLFormula, Boolean]] =
  {
    val clauses = soft.foldLeft(hard)((acc,c) => acc + c._1)
    updateAtoms(clauses)
    val sb = new StringBuilder()

    val nl = System.getProperty("line.separator")
    var top = 1
    if(soft.size == 0)
    {
      sb.append("p wcnf " + atom_map.size + " "  + clauses.size + nl)
    }
    else{
      top = soft.foldLeft(0)((acc,x) => acc + x._2) + 1
      sb.append("p wcnf " + atom_map.size + " "  + clauses.size + " " + top + nl)
    }

    // construct qmaxsat text input
    hard.foreach ( c =>
    {
      sb.append(getQMaxSATString(c, top))
      sb.append("0")
      sb.append(nl)
    } )
    soft.foreach ( c =>
    {
      sb.append(getQMaxSATString(c._1, c._2))
      sb.append("0")
      sb.append(nl)
    } )

    val temp_in = File.createTempFile("qmaxsat_in",".wcnf")
    temp_in.deleteOnExit()

    val temp_out = File.createTempFile("qmaxsat_out",".sol")
    temp_out.deleteOnExit()

    val stdout = File.createTempFile("qmaxsat",".stdout")
    stdout.deleteOnExit()

    val out = new BufferedWriter(new FileWriter(temp_in))
    out.append(sb.toString())
    out.close()

    trace( "Generated MiniSAT input: ")
    trace(sb.toString());

    // run qmaxsat

    //val run = pathToBinary + " " + temp_in.getAbsolutePath() + " " + temp_out.getAbsolutePath();
    debug("Starting qmaxsat...");
    val command = List(bin, temp_in.getAbsolutePath(), temp_out.getAbsolutePath())
    val process = Process(command)
    var output = new StringBuilder()
    var error = new StringBuilder()
    val processIO = new ProcessIO(
      _ => (), // stdin does not matter
      stdout => scala.io.Source.fromInputStream(stdout).getLines.foreach(s => output.append(s+"\n")),
      stderr => scala.io.Source.fromInputStream(stderr).getLines.foreach(s => error.append(s+"\n")))

    val value = process run processIO exitValue

    debug("Exit Value = " + value)
    debug("qmaxsat finished.");


    debug("IN_FILE:\n"+TextFileSlurper(temp_in));
    debug("OUT_FILE:\n"+TextFileSlurper(temp_out));
    debug("OUT:\n"+output.toString);
    debug("ERR:\n"+error.toString);
    // parse qmaxsat output and construct map
    val in = new BufferedReader(new InputStreamReader(
      new FileInputStream(stdout)));

    val sat = in.readLine();
    trace("QMaxSAT result: " + sat)
    var weight = 0
    if ( output.toString.startsWith("o") ) {
      val lines = output.toString.split("\n")
      weight = lines(0).split(" ")(1).toInt
      var result = ""
      for (l <- lines)
      {
        if (l.startsWith("v")){
          result = l
        }
      }
      Some( result.split(" ").
        filter(lit => !lit.equals("") && !lit.equals("v") && !lit.charAt(0).equals('0')).
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
