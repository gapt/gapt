package at.logic.gapt.provers.maxsat

import java.io._

import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.formats.dimacs.DIMACSHelper
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.models.{ MapBasedInterpretation, Interpretation }
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.utils.logging.{ metrics, Logger, Stopwatch }

import scala.collection.immutable.Map
import scala.sys.process.{ Process, ProcessIO }

/**
 * This trait provides an interface to solvers for the Weighted Partial MaxSat problem.
 */

trait MaxSATSolver extends Logger {

  protected def logTime( msg: String, millisec: Long ): Unit = {
    val msec = millisec % 1000
    val sec = ( millisec / 1000 ) % 60
    val minutes = ( ( millisec / 1000 ) / 60 ) % 60
    val hours = ( ( ( millisec / 1000 ) / 60 ) / 60 )
    debug( msg + " " + hours + "h " + minutes + "min " + sec + "sec " + msec + "msec" )
  }

  /**
   * @param hard Hard constraints in CNF.
   * @param soft Soft constraints in CNF along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solve( hard: List[HOLClause], soft: List[( HOLClause, Int )] ): Option[Interpretation]

  /**
   * @param hard Hard constraints.
   * @param soft Soft constraints along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solveWPM( hard: List[FOLFormula], soft: List[Tuple2[FOLFormula, Int]], watch: Stopwatch = new Stopwatch() ) = {
    debug( "Generating clauses..." )

    // Hard CNF transformation
    watch.start()
    val hardCNF = metrics.time( "tseitin" ) { TseitinCNF( And( hard ) ) }
    val hardCNFTime = watch.lap( "hardCNF" )
    logTime( "[Runtime]<hard CNF-Generation> ", hardCNFTime )
    trace( "produced hard cnf: " + hardCNF )

    // Soft CNF transformation
    watch.start()
    val softCNFs = soft.map( s => CNFp.toClauseList( s._1 ).map( f => ( f, s._2 ) ) ).flatten
    val softCNFTime = watch.lap( "softCNF" )
    logTime( "[Runtime]<soft CNF-Generation> ", softCNFTime )
    trace( "produced soft cnf: " + softCNFs )

    watch.start()
    val interpretation = solve( hardCNF, softCNFs )
    val solveTime = watch.lap( "MaxSAT" )
    logTime( "[Runtime]<solveMaxSAT> ", solveTime )

    interpretation
  }
}

class WDIMACSHelper( val hard: List[HOLClause], val soft: List[( HOLClause, Int )] )
    extends DIMACSHelper( hard ++ soft.map( _._1 ) ) {
  /**
   * Returns for a given atom and
   * polarization a String for a propositional Variable in .wcnf format
   * @param atom atom to provide
   * @param pol polarization (true, false)
   * @return a literal in .wcnf format
   */
  protected def getWCNFString( atom: FOLAtom, pol: Boolean, atom_map: Map[HOLAtom, Int] ): String =
    if ( pol ) atom_map.get( atom ).get.toString else "-" + atom_map.get( atom ).get

  /**
   * Returns for a given clause and weight
   * a representation of it in .wcnf format
   *
   * @param clause clause to provide
   * @param weight weight of clause
   * @return a clause in .wcnf format
   */
  protected def getWCNFString( clause: HOLClause, weight: Int, atom_map: Map[HOLAtom, Int] ): String =
    {
      val sb = new StringBuilder()

      sb.append( weight + " " )
      def atoms_to_str( as: Seq[FOLAtom], pol: Boolean ) = as.foreach( a => {
        sb.append( getWCNFString( a, pol, atom_map ) );
        sb.append( " " );
      } )

      atoms_to_str( clause.positive.asInstanceOf[Seq[FOLAtom]], true )
      atoms_to_str( clause.negative.asInstanceOf[Seq[FOLAtom]], false )

      sb.toString()
    }

  def getWCNFInput(): StringBuilder = {
    val sb = new StringBuilder()
    val nl = System.getProperty( "line.separator" )
    var top = 1
    if ( soft.size == 0 ) {
      sb.append( "p wcnf " + atom_map.size + " " + clauses.size + nl )
    } else {
      top = soft.foldLeft( 0 )( ( acc, x ) => acc + x._2 ) + 1
      sb.append( "p wcnf " + atom_map.size + " " + clauses.size + " " + top + nl )
    }

    // construct qmaxsat text input
    hard.foreach( c =>
      {
        sb.append( getWCNFString( c, top, atom_map ) )
        sb.append( "0" )
        sb.append( nl )
      } )
    soft.foreach( c =>
      {
        sb.append( getWCNFString( c._1, c._2, atom_map ) )
        sb.append( "0" )
        sb.append( nl )
      } )
    sb
  }
}

object readWDIMACS {
  /**
   * A delegator to treat outputformats of different MaxSAT Solvers differently
   * @param in output of sepcific MaxSAT Solver
   * @param helper The helper object used for this input/output session.
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  def apply( in: String, format: Format.Format, helper: WDIMACSHelper ): Option[Map[FOLFormula, Boolean]] =
    {
      format match {
        //case MaxSATSolver.QMaxSAT => {
        case Format.MultiVLine  => multiVLineOutputToInterpretation( in, helper )
        //}

        //case MaxSATSolver.ToySAT => {
        case Format.ToySAT      => toysatOutputToInterpretation( in, helper )
        //}
        //case MaxSATSolver.ToySolver => {
        //  multiVLineOutputToInterpretation( in )
        //}
        //case MaxSATSolver.MiniMaxSAT => {
        case Format.SingleVLine => singleVLineOutputToInterpretation( in, helper )
        //}
        case _                  => None
      }
    }
  /**
   * A method to treat outputformat of a MaxSATSolver with
   * a single line starting with a 'v'
   * @param in output string of the MaxSAT Solver
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  private def singleVLineOutputToInterpretation( in: String, helper: DIMACSHelper ): Option[Map[FOLFormula, Boolean]] = {

    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    ( oLinePattern findFirstIn in ) match {
      case None => None
      case Some( str ) => {
        var weight = str.split( " " )( 1 ).toInt
        ( vLinePattern findFirstIn in ) match {
          case None => None
          case Some( vline ) => {
            Some( vline.split( " " ).
              filter( lit => !lit.equals( "" ) && !lit.equals( "v" ) && !lit.charAt( 0 ).equals( '0' ) ).
              map( lit =>
                if ( lit.charAt( 0 ) == '-' ) {
                  // negative literal
                  ( helper.getAtom( lit.substring( 1 ).toInt ).get.asInstanceOf[FOLFormula], false )
                } else {
                  // positive literal
                  ( helper.getAtom( lit.toInt ).get.asInstanceOf[FOLFormula], true )
                } ).toSet.toMap )
          }
        }
      }
    }
  }

  /**
   * A method to treat outputformat of a MaxSATSolver with
   * multiple lines starting with a 'v'
   * @param str output string of the MaxSAT Solver
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  private def multiVLineOutputToInterpretation( str: String, helper: DIMACSHelper ): Option[Map[FOLFormula, Boolean]] = {
    val sLinePattern = """(?m)^s.*""".r
    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    val sat = ( sLinePattern findFirstIn str )
    if ( sat == None ) {
      return None
    } else {
      val satstrings = sat.get.split( " " )

      if ( satstrings.size > 1 && satstrings( 1 ) == "OPTIMUM" ) {
        val opt = ( oLinePattern findFirstIn str )
        var optstring = Array( "", "-1" )
        if ( opt != None ) {
          optstring = opt.get.split( " " )
        }

        var weight = optstring( 1 ).toInt
        // get all lines starting with v and drop the v
        val model = ( vLinePattern findAllIn str ).map( _.drop( 2 ).split( " " ) ).foldLeft( List[String]() )( ( v, acc ) => v ++ acc )
        return Some( model.
          filter( lit => !lit.equals( "" ) && !lit.equals( "v" ) && !lit.charAt( 0 ).equals( '0' ) ).
          map( lit =>
            if ( lit.charAt( 0 ) == '-' ) {
              // negative literal
              ( helper.getAtom( lit.substring( 1 ).toInt ).get.asInstanceOf[FOLFormula], false )
            } else {
              // positive literal
              ( helper.getAtom( lit.toInt ).get.asInstanceOf[FOLFormula], true )
            } )
          .toSet.toMap )
      }
    }
    return None
  }

  /**
   * A method to treat outputformat of the ToySAT
   * @param str output of ToySAT
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  private def toysatOutputToInterpretation( str: String, helper: DIMACSHelper ): Option[Map[FOLFormula, Boolean]] = {
    val sLinePattern = """(?m)^s.*""".r
    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    val sat = ( sLinePattern findFirstIn str )
    if ( sat == None ) {
      return None
    } else {
      val satstrings = sat.get.split( " " )

      if ( satstrings.size > 1 && satstrings( 1 ) == "OPTIMUM" ) {
        val opt = ( oLinePattern findFirstIn str )
        var optstring = Array( "", "-1" )
        if ( opt != None ) {
          optstring = opt.get.split( " " )
        }

        var weight = optstring( 1 ).toInt
        // get all lines starting with v and drop the v
        val model = ( vLinePattern findAllIn str ).map( _.drop( 2 ).split( " " ) ).foldLeft( List[String]() )( ( v, acc ) => v ++ acc )
        return Some( model.
          filter( lit => !lit.equals( "" ) && !lit.equals( "v" ) && !lit.charAt( 0 ).equals( '0' ) ).
          map( lit =>
            if ( lit.charAt( 0 ) == '-' ) {
              // negative literal
              // HERE IS 1 of 2 DIFFERENCES TO TOYSOLVER
              ( helper.getAtom( lit.substring( 2 ).toInt ).get.asInstanceOf[FOLFormula], false )
            } else {
              // positive literal
              // HERE IS 1 of 2 DIFFERENCES TO TOYSOLVER
              ( helper.getAtom( lit.substring( 1 ).toInt ).get.asInstanceOf[FOLFormula], true )
            } )
          .toSet.toMap )
      }
    }
    return None
  }
}

/**
 * A trait for such WCNF-based MaxSAT solvers that are invoked
 * by calling an OS-level binary.
 */
trait MaxSATSolverBinary extends MaxSATSolver {
  val nLine = sys.props( "line.separator" )

  /**
   * Constructs the input command list for Process from the
   * names of the input and output files for the MaxSAT solver.
   *  For examples, have a look at implementations of this trait.
   * @param in The name of the input file.
   * @param out The name of the output file.
   * @return The command list.
   */
  def command( in: String, out: String ): List[String]

  /**
   * A warning message to be displayed if the binary is not found.
   * @return A warning message to be displayed if the binary is not found.
   */
  def noBinaryWarn(): String

  /**
   * The output format of this prover.
   * @return
   */
  def format(): Format.Format

  /**
   * Checks if a particular Max SAT Solver is installed properly
   * @return true if it is installed, false otherwise
   */
  val isInstalled: Boolean = {
    try {
      val clause = HOLClause( List(), List( FOLAtom( "P" ) ) )
      solve( List( clause ), List( clause -> 1 ) ) match {
        case Some( _ ) => true
        case None      => throw new IOException()
      }
    } catch {
      case ex: IOException => {
        warn( "It seems that the MaxSAT solver is not installed properly" )
        warn( noBinaryWarn() )
        false
      }
    }
  }

  /**
   * Converts a given partial weighted MaxSAT instance
   * into wcnf format and invokes the solver via the supplied command.
   * If the instance is satisfiable a model is returned, otherwise None
   *
   * @param hard clause set of hardconstraints
   * @param soft clause set (+ weights) of soft constraints
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  protected def getFromMaxSATBinary( hard: List[HOLClause], soft: List[Tuple2[HOLClause, Int]] ): Option[Interpretation] =
    {
      debug( "Generating wcnf file..." )
      val helper = new WDIMACSHelper( hard, soft )
      val startTimeGenerate = System.currentTimeMillis()
      val input = helper.getWCNFInput()
      val endTimeGenerate = System.currentTimeMillis()
      logTime( "[Runtime]<wcnf-Generation> ", ( endTimeGenerate - startTimeGenerate ) )

      val temp_in = File.createTempFile( "maxsat_in", ".wcnf" )
      temp_in.deleteOnExit()

      val temp_out = File.createTempFile( "maxsat_out", ".sol" )
      temp_out.deleteOnExit()

      val stdout = File.createTempFile( "maxsat", ".stdout" )
      stdout.deleteOnExit()

      val stderr = File.createTempFile( "maxsat", ".stderr" )
      stderr.deleteOnExit()

      val startTimeWriteInput = System.currentTimeMillis()
      val out = new BufferedWriter( new FileWriter( temp_in ) )
      out.append( input.toString() )
      out.close()
      val endTimeWriteInput = System.currentTimeMillis()
      logTime( "[Runtime]<wcnf-IO> ", ( endTimeWriteInput - startTimeWriteInput ) )

      debug( "Starting maxsat..." )
      val startTimeMaxSAT = System.currentTimeMillis()

      var options = scala.collection.mutable.MutableList[String]()
      var command_ = command( temp_in.getAbsolutePath(), temp_out.getAbsolutePath() )

      debug( "Command: " + command_ )

      var output = new StringBuilder()
      var error = new StringBuilder()
      val processIO = new ProcessIO(
        _ => (), // stdin does not matter
        stdout => scala.io.Source.fromInputStream( stdout, "ISO-8859-1" ).getLines.foreach( s => output.append( s + nLine ) ),
        stderr => scala.io.Source.fromInputStream( stderr, "ISO-8859-1" ).getLines.foreach( s => error.append( s + nLine ) )
      )

      val proc = Process( command_ ) run processIO
      var value: Int = -1

      try {
        // run MaxSATSOlver process
        value = metrics.time( "maxsat_solver" ) { proc exitValue }
      } catch {
        // catch ThreadDeath if the procedure is interrupted by a Timeout
        // and kill the external MaxSATSolver process
        case tde: ThreadDeath => {
          debug( "Process interrupted by timeout: Killing MaxSATSolver process" );
          proc.destroy();
          value = proc.exitValue();
          throw tde;
        }
      }

      debug( "Exit Value = " + value )
      debug( "maxsat finished" )
      logTime( "[Runtime]<maxsat> ", ( System.currentTimeMillis() - startTimeMaxSAT ) )

      trace( "IN_FILE:" + nLine + scala.io.Source.fromFile( temp_in, "UTF-8" ).mkString );
      //debug("OUT_FILE:" + nLine +TextFileSlurper(temp_out));
      trace( "OUT:" + nLine + output.toString );
      trace( "ERR:" + nLine + error.toString );
      // parse maxsat output and construct map
      val in = new BufferedReader( new InputStreamReader(
        new FileInputStream( stdout )
      ) );

      //val str = Stream.continually(in.readLine()).takeWhile(_ != null).mkString(nLine)

      readWDIMACS( output.toString(), format(), helper ) match {
        case Some( model ) => Some( new MapBasedInterpretation( model.asInstanceOf[Map[HOLFormula, Boolean]] ) )
        case None          => None
      }
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

/**
 * An enumeration to distinguish different output formats of
 * WCNF-based MaxSAT solvers.
 *
 */
object Format extends Enumeration {
  type Format = Value
  val MultiVLine, ToySAT, SingleVLine = Value
}
