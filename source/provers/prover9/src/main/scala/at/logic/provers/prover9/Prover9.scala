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
import at.logic.provers.prover9.ivy.IvyParser
import at.logic.provers.prover9.ivy.conversion.IvyToRobinson
import at.logic.calculi.resolution.robinson.{InitialClause, RobinsonResolutionProof}
import java.io.File
import at.logic.provers.prover9.ivy.IvyParser.{IvyStyleVariables, PrologStyleVariables, LadrStyleVariables}

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

  def p9_to_ivy( input_file: String, output_file: String ) : Int = {
    val ret = exec("prooftrans ivy", input_file )
//    println("prooftrans output:")
//    println(ret._2)
    writeToFile( ret._2, output_file )
    ret._1
  }

  def refuteNamed( named_sequents : List[Pair[String, FSequent]], input_file: String, output_file: String ) : Option[RobinsonResolutionProof] =
  {
    val tmp_file = File.createTempFile( "gapt-prover9", ".tptp", null )
    writeProblem( named_sequents, tmp_file )

    tptpToLadr( tmp_file.getAbsolutePath, input_file )
    tmp_file.delete
    refuteLadr(input_file, output_file)
  }


    def refuteLadr( input_file: String, output_file: String ) : Option[RobinsonResolutionProof] = {
    // find out which symbols have been renamed
    // this information should eventually be used when
    // parsing the prover9 proof
    val regexp = new Regex("""%\s*\(arity (\d+)\)\s*'(.*?)'\s*(ladr\d+)""")
   
    val str_ladr = Source.fromInputStream( new FileInputStream( input_file ) ).mkString

    val map = str_ladr.split(System.getProperty("line.separator")).foldLeft(new HashMap[String, (Int,String)])( (m, l) =>
      l match {
        case regexp(arity, orig, repl ) => m.updated( orig, (arity.toInt , repl) )
        case _ => m
    })

    println( "translation map: " )
    println( map )

    val ret = refute( input_file, output_file )
    ret match {
      case 0 =>
        try  {
          Some(parse_prover9(output_file))
        } catch {
          case e : Exception =>
            println("Warning: Prover9 run successfully but conversion to resolution proof failed! " + e.getMessage)
            Some(InitialClause(Nil,Nil))
        }
      case 1 => throw new Prover9Exception("A fatal error occurred (user's syntax error or Prover9's bug).")
      case 2 => None // Prover9 ran out of things to do (sos list exhausted).
      case 3 => None // The max_megs (memory limit) parameter was exceeded.
      case 4 => None // The max_seconds parameter was exceeded.
      case 5 => None // The max_given parameter was exceeded.
      case 6 => None // The max_kept parameter was exceeded.
      case 7 => None // A Prover9 action terminated the search.
      case 101 => throw new Prover9Exception("Prover9 received an interrupt signal.")
      case 102 => throw new Prover9Exception("Prover9 crashed, most probably due to a bug.")
    }
  }

  def refute( sequents: List[FSequent], input_file: String, output_file: String ) : Option[RobinsonResolutionProof] =
    refuteNamed( sequents.zipWithIndex.map( p => ("sequent" + p._2, p._1) ), input_file, output_file )

  def refute( sequents: List[FSequent] ) : Option[RobinsonResolutionProof] = {
    val in_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    val ret = refute( sequents, in_file.getAbsolutePath, out_file.getAbsolutePath )
    in_file.delete
    out_file.delete
    ret
  }

  def refute( filename : String ) : Option[RobinsonResolutionProof] = {
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    val ret = refuteLadr(new File(filename).getAbsolutePath, out_file.getAbsolutePath )
    out_file.delete
    ret
  }


  def parse_prover9(p9_file : String) : RobinsonResolutionProof = {
    val ivy_file = File.createTempFile( "gapt-prover9", ".ivy", null )
    p9_to_ivy(p9_file, ivy_file.getCanonicalPath)
    def debugline(s:String) = { println(s); true}

    /* //this was autodetection code for naming conventions, but apparently ivy has its own anyway
    val variablestyle_matcher = """prolog_style_variables""".r
    val str_p9 = Source.fromInputStream( new FileInputStream( p9_file ) ).mkString
    val set_prolog_style_variables = for (line <- str_p9.split(System.getProperty("line.separator"));
         if ( debugline(line) && variablestyle_matcher.findFirstIn(line).isDefined)) yield line

    val iproof = if (set_prolog_style_variables.isEmpty) {
                    println("Detected Ladr Naming Style!")
                    IvyParser(ivy_file.getCanonicalPath, LadrStyleVariables)
                  }
                  else {
                    println("Detected Prolog Naming Style!")
                    IvyParser(ivy_file.getCanonicalPath, PrologStyleVariables)
                  }*/
    val iproof = IvyParser(ivy_file.getCanonicalPath, IvyStyleVariables)
    val rproof = IvyToRobinson(iproof)
    ivy_file.delete
    rproof
  }

}
