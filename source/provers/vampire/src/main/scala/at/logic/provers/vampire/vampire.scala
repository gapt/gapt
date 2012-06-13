/**
 * Interface to the Prover9 first-order theorem prover.
 * Needs the command-line tools prover9 and tptp_to_ladr
 * to work.
 */

package at.logic.provers.vampire

import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol._
import at.logic.parsing.language.tptp.TPTPFOLExporter
import java.io._
import scala.io.Source
import scala.util.matching.Regex
import scala.collection.immutable.HashMap

class VampireException(msg: String) extends Exception(msg)

object Vampire {

  def writeProblem( named_sequents: List[Pair[String, FSequent]], file_name: String ) =
  {

    val tptp = TPTPFOLExporter.tptp_problem_named( named_sequents )
    //println("created tptp input: " + tptp)
    val writer = new FileWriter( file_name )
    writer.write( tptp )
    writer.flush
  }

  // TODO: this does not really belong here, refactor?
  // executes "prog" and feeds the contents of the file at
  // path "in" to its standard input.
  private def exec( prog_alternatives: List[String], in: String ) : (Int, String) =
  {
    for (prog <- prog_alternatives) {
      try {
        val p = Runtime.getRuntime.exec( prog )

        val out = new OutputStreamWriter( p.getOutputStream )
        out.write( Source.fromInputStream( new FileInputStream( in ) ).mkString )
        out.close

        val str = Source.fromInputStream( p.getInputStream ).mkString
        p.waitFor
        ( p.exitValue, str )
      } catch {
        case e : IOException => println("could not find binary "+prog+" in path!");
      }
    }

    throw new VampireException("Could not execute vampire binary!")
  }

  def writeToFile( str: String, file: String ) = {
    val out = new FileWriter( file )
    out.write( str )
    out.close
  }

  def refute( input_file: String, output_file: String ) : Int = {
    //TODO: find correct binary (lin32, lin64, mac)
    val ret = exec(List("vampire_lin64","vampire_lin32","vampire_macosx"), input_file )
    writeToFile( ret._2, output_file )
    ret._1
  }

  def refuteNamed( named_sequents : List[Pair[String, FSequent]], input_file: String, output_file: String ) : Boolean =
  {
    writeProblem( named_sequents, input_file )

    val ret = refute( input_file, output_file )
    ret match {
      case 0 => true
      case _ => throw new VampireException("The set was satisfiable or there was a problem executing vampire!")
    }
  }

  def refute( sequents: List[FSequent], input_file: String, output_file: String ) : Boolean =
    refuteNamed( sequents.zipWithIndex.map( p => ("sequent" + p._2, p._1) ), input_file, output_file )

  def refute( sequents: List[FSequent] ) : Boolean = {
    val in_file = File.createTempFile( "gapt-vampire", ".tptp", null )
    val out_file = File.createTempFile( "gapt-vampire", "prover9", null )
    val ret = refute( sequents, in_file.getAbsolutePath, out_file.getAbsolutePath )
    in_file.delete
    out_file.delete
    ret
  }

}
