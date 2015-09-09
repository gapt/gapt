/**
 * Interface to the Vampire first-order theorem prover.
 */

package at.logic.gapt.provers.vampire

import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.formats.tptp.TPTPFOLExporter

import java.io._
import at.logic.gapt.utils.logging.Logger

import scala.io.Source

class VampireException( msg: String ) extends Exception( msg )

object Vampire extends Logger {

  def writeProblem( named_sequents: List[Tuple2[String, HOLSequent]], file_name: String ) =
    {
      val tptp = TPTPFOLExporter.tptp_problem_named( named_sequents )
      val writer = new FileWriter( file_name )
      writer.write( tptp )
      writer.flush
    }

  // TODO: this does not really belong here, refactor?
  // executes "prog" and feeds the contents of the file at
  // path "in" to its standard input.
  private def exec( in: String ): ( Int, String ) = {
    if ( !vampireBinaryName.isDefined )
      throw new VampireException( "Unable to determine vampire's binary name for your OS!" )
    val prog = vampireBinaryName.get
    val p = Runtime.getRuntime.exec( prog )

    val out = new OutputStreamWriter( p.getOutputStream )
    out.write( Source.fromInputStream( new FileInputStream( in ) ).mkString )
    out.close

    val str = Source.fromInputStream( p.getInputStream ).mkString
    p.waitFor
    ( p.exitValue, str )
  }

  def writeToFile( str: String, file: String ) = {
    val out = new FileWriter( file )
    out.write( str )
    out.close
  }

  def refute( input_file: String, output_file: String ): ( Int, String ) = {
    val ret = exec( input_file )
    writeToFile( ret._2, output_file )
    ret
  }

  def refuteNamed( named_sequents: List[Tuple2[String, HOLSequent]], input_file: String, output_file: String ): Boolean =
    {
      writeProblem( named_sequents, input_file )

      val ret = refute( input_file, output_file )
      ret._1 match {
        case 0 if ret._2.startsWith( "Refutation found" ) => true
        case 0 if ret._2.startsWith( "Satisfiable" ) => false
        case _ => throw new VampireException( "There was a problem executing vampire!" )
      }
    }

  def refute( sequents: List[HOLSequent], input_file: String, output_file: String ): Boolean =
    refuteNamed( sequents.zipWithIndex.map( p => ( "sequent" + p._2, p._1 ) ), input_file, output_file )

  def refute( sequents: List[HOLSequent] ): Boolean = {
    val in_file = File.createTempFile( "gapt-vampire", ".tptp", null )
    val out_file = File.createTempFile( "gapt-vampire", "vampire", null )
    in_file.deleteOnExit()
    out_file.deleteOnExit()
    val ret = refute( sequents, in_file.getAbsolutePath, out_file.getAbsolutePath )
    in_file.delete
    out_file.delete
    ret
  }

  val vampireBinaryName: Option[String] = {
    val osName = System.getProperty( "os.name" ).toLowerCase()
    val osArch = System.getProperty( "os.arch" )
    osName match {
      case osName if osName.contains( "mac" ) => Some( "vampire_mac" )
      case osName if osName.contains( "linux" ) && osArch.contains( "64" ) => Some( "vampire_lin64" )
      case osName if osName.contains( "linux" ) && osArch.contains( "32" ) => Some( "vampire_lin32" )
      case _ => None
    }
  }

  def isInstalled(): Boolean = {
    val box = List()
    try {
      Vampire.refute( box )
    } catch {
      case e: IOException =>
        warn( e.getMessage )
        return false
    }
    return true
  }

}
