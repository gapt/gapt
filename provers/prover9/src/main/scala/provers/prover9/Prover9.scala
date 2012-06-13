/**
 * Interface to the Prover9 first-order theorem prover.
 * Needs the command-line tools prover9 and tptp_to_ladr
 * to work.
 */

package at.logic.provers.prover9

import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol._
import at.logic.parsing.language.tptp.TPTPFOLExporter
import java.io._
import scala.io.Source
import scala.util.matching.Regex
import scala.collection.immutable.HashMap
import at.logic.calculi.lk.base.types.FSequent

class Prover9Exception(msg: String) extends Exception(msg)

object Prover9 {

  def writeProblem( named_sequents: List[Pair[String, FSequent]], file: File ) = 
  {
    val tptp = TPTPFOLExporter.tptp_problem_named( named_sequents )
    //println("created tptp input: " + tptp)
    val writer = new FileWriter( file )
    writer.write( tptp )
    writer.flush
  }

  // TODO: this does not really belong here, refactor?
  // executes "prog" and feeds the contents of the file at
  // path "in" to its standard input.
  private def exec( prog: String, in: String ) =
  {
    val p = Runtime.getRuntime.exec( prog )

    val out = new OutputStreamWriter( p.getOutputStream )
    out.write( Source.fromInputStream( new FileInputStream( in ) ).mkString )
    out.close

    val str = Source.fromInputStream( p.getInputStream ).mkString
    p.waitFor
    ( p.exitValue, str )
  }

  def tptpToLadr( tptp: String, ladr: String ) = {
    val ret = exec("tptp_to_ladr", tptp)
    //println( "writing ladr to: " + ladr )
    val str_ladr = ret._2
    writeToFile( str_ladr, ladr )
    ret._1
  }

  def writeToFile( str: String, file: String ) = {
    val out = new FileWriter( file )
    out.write( str )
    out.close
  }

  def refute( input_file: String, output_file: String ) : Int = {
    val ret = exec("prover9", input_file )
    writeToFile( ret._2, output_file )
    ret._1
  }

  def refuteNamed( named_sequents : List[Pair[String, FSequent]], input_file: String, output_file: String ) : Boolean = 
  {
    val tmp_file = File.createTempFile( "gapt-prover9", ".tptp", null )
    writeProblem( named_sequents, tmp_file )

    tptpToLadr( tmp_file.getAbsolutePath, input_file )
    tmp_file.delete
    
    // find out which symbols have been renamed
    // this information should eventually be used when
    // parsing the prover9 proof
    val regexp = new Regex("""%\s*\(arity \d+\)\s*'(.*?)'\s*(ladr\d+)""")
   
    val str_ladr = Source.fromInputStream( new FileInputStream( input_file ) ).mkString

    val map = str_ladr.split(System.getProperty("line.separator")).foldLeft(new HashMap[String, String])( (m, l) => 
      l match {
        case regexp( orig, repl ) => m.updated( orig, repl )
        case _ => m
    })

    //println( "translation map: " )
    //println( map )

    val ret = refute( input_file, output_file )
    ret match {
      case 0 => true
      case 1 => throw new Prover9Exception("A fatal error occurred (user's syntax error or Prover9's bug).")
      case 2 => false // Prover9 ran out of things to do (sos list exhausted).
      case 3 => false // The max_megs (memory limit) parameter was exceeded. 
      case 4 => false // The max_seconds parameter was exceeded.
      case 5 => false // The max_given parameter was exceeded. 
      case 6 => false // The max_kept parameter was exceeded. 
      case 7 => false // A Prover9 action terminated the search.
      case 101 => throw new Prover9Exception("Prover9 received an interrupt signal.")
      case 102 => throw new Prover9Exception("Prover9 crashed, most probably due to a bug.")
    }
  }

  def refute( sequents: List[FSequent], input_file: String, output_file: String ) : Boolean = 
    refuteNamed( sequents.zipWithIndex.map( p => ("sequent" + p._2, p._1) ), input_file, output_file )

  def refute( sequents: List[FSequent] ) : Boolean = {
    val in_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    val ret = refute( sequents, in_file.getAbsolutePath, out_file.getAbsolutePath )
    in_file.delete
    out_file.delete
    ret
  }

}
