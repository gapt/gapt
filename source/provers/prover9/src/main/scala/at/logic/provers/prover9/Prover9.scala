/**
 * Interface to the Prover9 first-order theorem prover.
 * Needs the command-line tools prover9, prooftool and tptp_to_ladr
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
import at.logic.parsing.ivy.IvyParser
import at.logic.parsing.ivy.conversion.IvyToRobinson
import at.logic.calculi.resolution.robinson.{InitialClause, RobinsonResolutionProof}
import java.io.File
import at.logic.parsing.ivy.IvyParser.{IvyStyleVariables, PrologStyleVariables, LadrStyleVariables}
import at.logic.algorithms.rewriting.NameReplacement
import at.logic.algorithms.resolution.InstantiateElimination
import at.logic.provers.prover9.commands.InferenceExtractor
import at.logic.parsing.language.prover9._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.calculi.lk.propositionalRules.{CutRule, Axiom}

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

  def exec_in_out( cmd : String, in: String, out: String ) = {
    val ret = exec(cmd, in)
    val str_ladr = ret._2
    writeToFile( str_ladr, out )
    ret._1
  }

  def writeToFile( str: String, file: String ) = {
    val out = new FileWriter( file )
    out.write( str )
    out.close
  }

  /* these are shortcuts for executing the programs; all take an input and an output file and
     return the exit status of the tool used */
  def tptpToLadr(in:String, out:String) = exec_in_out("tptp_to_ladr",in,out)
  def refute(in:String, out:String) = exec_in_out("prover9",in,out)
  def p9_to_ivy(in:String, out:String) = exec_in_out("prooftrans ivy",in,out)
  def p9_to_p9(in:String, out:String) = exec_in_out("prooftrans",in,out)



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

    val symbol_map = str_ladr.split(System.getProperty("line.separator")).foldLeft(new HashMap[String, (Int,String)])( (m, l) =>
      l match {
        case regexp(arity, orig, repl ) => m.updated( repl , (arity.toInt , orig) )
        case _ => m
    })

//    println( "translation map: " )
//    println( symbol_map )

    val ret = refute( input_file, output_file )
    ret match {
      case 0 =>
        try  {
          val p9proof = parse_prover9(output_file, false)
          val tp9proof = NameReplacement(p9proof._1, symbol_map)
          //println("applied symbol map: "+symbol_map+" to get endsequent "+tp9proof.root)

          Some(tp9proof)
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

  def refuteTPTP(fn : String) : Option[RobinsonResolutionProof] = {
    val out_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    tptpToLadr(fn, out_file.getAbsolutePath )
    val proof = refute(out_file.getAbsolutePath)
    out_file.delete
    proof
  }

  def getVar(t:LambdaExpression, l:Set[(Int,String)]) : Set[(Int,String)] = t match {
    case Var(ConstantStringSymbol(s),_) => l+((0,s)) ;
    case Var(_,_) => l;
    case AppN(Var(ConstantStringSymbol(s),_),ts) => ts.foldLeft(l)((x: Set[(Int,String)], y:LambdaExpression) => x ++ getVar(y, x) ) + ((ts.size,s))
    case App(s,t) => getVar(s, getVar(t,l))
    //case AppN(s,ts) => getVar(s, ts.foldLeft(l)((x: Set[(Int,String)], y:LambdaExpression) => x ++ getVar(y, x) ))
    case Abs(_,s) => getVar(s,l)
  }


  //def escape_constants[T<:LambdaExpression](r:RobinsonResolutionProof, f:T) : (RobinsonResolutionProof,T) = {}
  def escape_constants(r:RobinsonResolutionProof, f:FSequent) : (RobinsonResolutionProof,FSequent) = {
    val names : Set[(Int,String)] = r.nodes.map( _.asInstanceOf[RobinsonResolutionProof].root.occurrences.map((fo:FormulaOccurrence) => getVar(fo.formula,Set[(Int,String)]()))).flatten.flatten
    val pairs : Set[(String, (Int,String))] = (names.map((x:(Int,String)) =>
      (x._2, ((x._1, x._2.replaceAll("_","\\\\_")))   ))
      )

    val mapping = NameReplacement.emptySymbolMap ++ (pairs)

    (NameReplacement.apply(r, mapping), NameReplacement(f,mapping))
  }


  /* Takes the output of prover9, extracts a resolution proof and the endsequent. */
  def parse_prover9(p9_file : String, escape_underscore : Boolean = true, newimpl : Boolean = true) : (RobinsonResolutionProof, FSequent) = {
    //println((new File(".")).getCanonicalPath)

    val pt_file = File.createTempFile( "gapt-prover9", ".pt", null )
    p9_to_p9(p9_file, pt_file.getCanonicalPath)
    val ivy_file = File.createTempFile( "gapt-prover9", ".ivy", null )
    p9_to_ivy(pt_file.getCanonicalPath, ivy_file.getCanonicalPath)

    def debugline(s:String) = { println(s); true}

    val iproof = IvyParser(ivy_file.getCanonicalPath, IvyStyleVariables)
    val rproof = IvyToRobinson(iproof)
    //val mproof = InstantiateElimination(rproof)
    val mproof = rproof
    pt_file.delete
    ivy_file.delete

//    val fs = Prover9TermParser.normalizeFSequent(InferenceExtractor(p9_file))

    val fs = if (newimpl) InferenceExtractor.viaLADR(p9_file) else InferenceExtractor.viaXML(p9_file)
    //println("extracted formula: "+fs)
    val (eproof, efs) = if (escape_underscore) escape_constants(mproof, fs)  else (mproof, fs)


    (eproof, efs)

  }

}
