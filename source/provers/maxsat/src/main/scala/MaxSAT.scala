/**
 * Created by spoerk on 6/23/14.
 */
package at.logic.provers.maxsat

import java.io._

import at.logic.algorithms.resolution.CNFp
import at.logic.calculi.resolution._
import at.logic.language.fol._
import at.logic.provers.maxsat.MaxSATSolver.MaxSATSolver
import scala.collection.immutable.HashMap
import scala.collection.mutable
import scala.sys.process.{Process, ProcessIO}

// This is also occuring in the minisat package
// TODO: refactoring
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

class MapBasedInterpretation( val model : Map[FOLFormula, Boolean]) extends Interpretation {
  def interpretAtom(atom : FOLFormula) = model.get(atom) match {
    case Some(b) => b
    case None => false
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

object MaxSATSolver extends Enumeration{
  type MaxSATSolver = Value
  val QMaxSAT, ToySAT, ToySolver = Value
}

// Call a MaxSAT solver to solve partial weighted MaxSAT instances
class MaxSAT(solver: MaxSATSolver) extends at.logic.utils.logging.Logger {

  val qmaxsatbin = "qmaxsat"
  val toysolverbin = "toysolver"
  val toysatbin = "toysat"



  def isInstalled() : Boolean = {
    try {
      val box : Set[FClause] = Set.empty
      solve(box,box.zipWithIndex)
      true
    } catch  {
      case ex: IOException => {
        warn("It seems that "+solver+" is not installed properly")
        solver match {
          case MaxSATSolver.QMaxSAT => warn("Please put the qmaxsat binary (available at https://sites.google.com/site/qmaxsat/) into PATH")
          case MaxSATSolver.ToySAT => warn("Please put the toysat binary (available at https://github.com/msakai/toysolver) into PATH")
          case MaxSATSolver.ToySolver => warn("Please put the toysolver binary (available at https://github.com/msakai/toysolver) into PATH")
        }
        return false
      }
    }
    return true
  }


  var atom_map : Map[FOLFormula, Int] = new HashMap[FOLFormula,Int]

  // Returns a model of a partial weighted MaxSAT instance, where
  // hard are the hard constraints and
  // soft are the soft constraints with weights w,
  // obtained from the QMaxSAT solver.
  // Returns None if unsatisfiable.
  def solvePWM( hard: Set[FOLFormula], soft: Set[Tuple2[FOLFormula, Int]] ) : Option[MapBasedInterpretation] = {
    val hardCNF = hard.foldLeft(Set[FClause]())((acc,f) => acc ++ CNFp(f))
    val softCNFs = soft.foldLeft(Set[Tuple2[FClause,Int]]())((acc,s) => acc ++ CNFp(s._1).foldLeft(Set[Tuple2[FClause,Int]]())((acc,f) => acc + Tuple2[FClause,Int](f, s._2) ))
    trace("produced hard cnf: " + hardCNF)
    trace("produced soft cnf: " + softCNFs)
    solve( hardCNF, softCNFs )
  }

  // Returns a model of the set of clauses obtained from the MiniSAT SAT solver.
  // Returns None if unsatisfiable.
  def solve( hardCNF: Set[FClause], softCNFs: Set[Tuple2[FClause,Int]] ) : Option[MapBasedInterpretation] =
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
      debug("TOP: "+top)
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

    val temp_in = File.createTempFile("maxsat_in",".wcnf")
    temp_in.deleteOnExit()

    val temp_out = File.createTempFile("maxsat_out",".sol")
    temp_out.deleteOnExit()

    val stdout = File.createTempFile("maxsat",".stdout")
    stdout.deleteOnExit()

    val stderr = File.createTempFile("maxsat",".stderr")
    stderr.deleteOnExit()

    val out = new BufferedWriter(new FileWriter(temp_in))
    out.append(sb.toString())
    out.close()

    //debug( "Generated maxsat input: ")
    //debug(sb.toString());

    // run maxsat

    //val run = pathToBinary + " " + temp_in.getAbsolutePath() + " " + temp_out.getAbsolutePath();
    debug("Starting maxsat...");
    var bin = qmaxsatbin
    var options = mutable.MutableList[String]()
    var command = List[String]()
    solver match {
      case MaxSATSolver.QMaxSAT => {
        command = List(qmaxsatbin, temp_in.getAbsolutePath(), temp_out.getAbsolutePath())
        bin = qmaxsatbin
      }
      case MaxSATSolver.ToySAT => {
        command = List(toysatbin, "--maxsat", temp_in.getAbsolutePath())
      }
      case MaxSATSolver.ToySolver => {
        command = List(toysolverbin, "--maxsat", temp_in.getAbsolutePath())
      }
    }

    debug("Command: "+command)
    val process = Process(command)
    var output = new StringBuilder()
    var error = new StringBuilder()
    val processIO = new ProcessIO(
      _ => (), // stdin does not matter
      stdout => scala.io.Source.fromInputStream(stdout, "ISO-8859-1").getLines.foreach(s => output.append(s+"\n")),
      stderr => scala.io.Source.fromInputStream(stderr, "ISO-8859-1").getLines.foreach(s => error.append(s+"\n")))

    val value = process run processIO exitValue

    debug("Exit Value = " + value)
    debug("maxsat finished.");


    debug("IN_FILE:\n"+TextFileSlurper(temp_in));
    //debug("OUT_FILE:\n"+TextFileSlurper(temp_out));
    debug("OUT:\n"+output.toString);
    debug("ERR:\n"+error.toString);
    // parse maxsat output and construct map
    val in = new BufferedReader(new InputStreamReader(
      new FileInputStream(stdout)));

    //val str = Stream.continually(in.readLine()).takeWhile(_ != null).mkString("\n")

    outputToInterpretation(output.toString)
  }

  private def outputToInterpretation(in: String) : Option[Map[FOLFormula, Boolean]] = {
    solver match {
      case MaxSATSolver.QMaxSAT => {
        qmaxsatOutputToInterpretation(in)
      }
      case MaxSATSolver.ToySAT => {
        toysatOutputToInterpretation(in)
      }
      case MaxSATSolver.ToySolver => {
        toysolverOutputToInterpretation(in)
      }
      case _ => None
    }
  }

  private def qmaxsatOutputToInterpretation(in: String) : Option[Map[FOLFormula, Boolean]] = {

    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    (oLinePattern findFirstIn in)match {
      case None => None
      case Some(str) => {
        var weight = str.split(" ")(1).toInt
        debug("weight: "+weight)
        (vLinePattern findFirstIn in) match{
          case None => None
          case Some(vline) => {
            debug("model: " + vline)
            Some(vline.split(" ").
              filter(lit => !lit.equals("") && !lit.equals("v") && !lit.charAt(0).equals('0')).
              map(lit =>
              if (lit.charAt(0) == '-') {
                // negative literal
                (getAtom(lit.substring(1).toInt).get, false)
              } else {
                // positive literal
                (getAtom(lit.toInt).get, true)
              })
              .toSet.toMap)
          }
        }
      }
    }
  }

  private def toysolverOutputToInterpretation(str: String) : Option[Map[FOLFormula, Boolean]] = {
    val sLinePattern = """(?m)^s.*""".r
    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    val sat = (sLinePattern findFirstIn str)
    if(sat == None){
      return None
    }
    else{
      val satstrings = sat.get.split(" ")

    if(satstrings.size > 1 && satstrings(1) == "OPTIMUM"){
        val opt = (oLinePattern findFirstIn str)
        var optstring = Array("", "-1")
        if(opt != None){
          optstring = opt.get.split(" ")
        }


        var weight = optstring(1).toInt
        // get all lines starting with v and drop the v
        val model = (vLinePattern findAllIn str).map(_.drop(2).split(" ")).foldLeft(List[String]())((v,acc) => v ++ acc)
        return Some( model.
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
      }
    }
    return None
  }

  private def toysatOutputToInterpretation(str: String) : Option[Map[FOLFormula, Boolean]] = {
    val sLinePattern = """(?m)^s.*""".r
    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    val sat = (sLinePattern findFirstIn str)
    if(sat == None){
      return None
    }
    else{
      val satstrings = sat.get.split(" ")

      if(satstrings.size > 1 && satstrings(1) == "OPTIMUM"){
        val opt = (oLinePattern findFirstIn str)
        var optstring = Array("", "-1")
        if(opt != None){
          optstring = opt.get.split(" ")
        }


        var weight = optstring(1).toInt
        // get all lines starting with v and drop the v
        val model = (vLinePattern findAllIn str).map(_.drop(2).split(" ")).foldLeft(List[String]())((v,acc) => v ++ acc)
        return Some( model.
          filter(lit => !lit.equals("") && !lit.equals("v") && !lit.charAt(0).equals('0')).
          map( lit =>
          if (lit.charAt(0) == '-') {
            // negative literal
            // HERE IS 1 of 2 DIFFERENCES TO TOYSOLVER
            (getAtom(lit.substring(2).toInt).get, false)
          } else {
            // positive literal
            // HERE IS 1 of 2 DIFFERENCES TO TOYSOLVER
            (getAtom(lit.substring(1).toInt).get, true)
          })
          .toSet.toMap)
      }
    }
    return None
  }
}
