/**
 * Interface to the Prover9 first-order theorem prover.
 * Needs the command-line tools prover9, prooftool and tptp_to_ladr
 * to work.
 */

package at.logic.gapt.provers.prover9

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.language.hol.containsStrongQuantifier
import at.logic.gapt.proofs.lk.algorithms.applyReplacement
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk.{ CutRule, Axiom }
import at.logic.gapt.proofs.resolution.{ FClause, Clause }
import at.logic.gapt.proofs.resolution.algorithms._
import at.logic.gapt.proofs.resolution.robinson.{ InitialClause, RobinsonResolutionProof }
import at.logic.gapt.language.fol._
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.IvyParser.{ IvyStyleVariables, PrologStyleVariables, LadrStyleVariables }
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.formats.prover9._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.prover9.commands.InferenceExtractor
import java.io._
import at.logic.gapt.utils.logging.Logger
import org.slf4j.LoggerFactory

import scala.sys.process._
import scala.collection.immutable.HashMap
import scala.io.Source
import scala.util.matching.Regex

class Prover9Exception( msg: String ) extends Exception( msg )

object Prover9 extends at.logic.gapt.utils.logging.Logger {

  private def writeProofProblem( seq: FSequent, file: File ) =
    {
      val tptp = TPTPFOLExporter.tptp_proof_problem( seq )
      trace( "created tptp input: " + tptp )
      val writer = new FileWriter( file )
      writer.write( tptp )
      writer.flush
    }

  private def writeRefutationProblem( named_sequents: List[Tuple2[String, FSequent]], file: File ) =
    {
      val tptp = TPTPFOLExporter.tptp_problem_named( named_sequents )
      trace( "created tptp input: " + tptp )
      val writer = new FileWriter( file )
      writer.write( tptp )
      writer.flush
    }

  // TODO: this does not really belong here, refactor?
  // executes "prog" and feeds the contents of the file at
  // path "in" to its standard input.
  private def exec( prog: String, in: String ) =
    {
      // FIXME this line throws an exception if tptp_to_ladr is not installed!
      val p = Runtime.getRuntime.exec( prog )

      val out = new OutputStreamWriter( p.getOutputStream )
      out.write( Source.fromInputStream( new FileInputStream( in ) ).mkString )
      out.close

      val str = Source.fromInputStream( p.getInputStream ).mkString
      p.waitFor
      ( p.exitValue, str )
    }

  private def exec_in_out( cmd: String, in: String, out: String ) = {
    val ret = exec( cmd, in )
    val str_ladr = ret._2
    writeToFile( str_ladr, out )
    ret._1
  }

  private def writeToFile( str: String, file: String ) = {
    val out = new FileWriter( file )
    out.write( str )
    out.close
  }

  /* these are shortcuts for executing the programs; all take an input and an output file and
     return the exit status of the tool used */
  private def tptpToLadr( in: String, out: String ) = exec_in_out( "tptp_to_ladr", in, out )
  private def runP9( in: String, out: String ) = exec_in_out( "prover9", in, out )
  private def p9_to_ivy( in: String, out: String ) = exec_in_out( "prooftrans ivy", in, out )
  private def p9_to_p9( in: String, out: String ) = exec_in_out( "prooftrans", in, out )

  /* Check if a sequent is valid using prover9 without parsing the proof */
  def isValid( seq: FSequent ): Boolean = {
    val in_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    in_file.deleteOnExit()
    out_file.deleteOnExit()
    val ret = isValid( seq, in_file.getAbsolutePath, out_file.getAbsolutePath )
    in_file.delete
    out_file.delete
    ret
  }

  private def isValid( seq: FSequent, input_file: String, output_file: String ): Boolean = {
    val tmp_file = File.createTempFile( "gapt-prover9-proof", ".tptp", null )
    tmp_file.deleteOnExit()
    writeProofProblem( seq, tmp_file )

    tptpToLadr( tmp_file.getAbsolutePath, input_file )
    tmp_file.delete
    isValid( input_file, output_file )
  }

  private def fileContainsProof( file: String ): Boolean = {
    val proof_str = "============================== PROOF ================================="
    val s = scala.io.Source.fromFile( file )
    val ret = s.getLines.exists( line => line.startsWith( proof_str ) )
    s.close()
    ret
  }

  private def isValid( input_file: String, output_file: String ): Boolean = {
    trace( "running prover9" )
    val ret = runP9( input_file, output_file )
    trace( "prover9 finished" )
    ret match {
      case 0 => // prover9 ran successfully
        return true
      case 1 => throw new Prover9Exception( "A fatal error occurred (user's syntax error or Prover9's bug)." )
      case 2 => {
        trace( "Prover9 ran out of things to do (sos list exhausted)." )
        // Sometimes, prover9 returns with this exit code even though
        // a proof has been found. 
        //
        // Hence we look through the proof for evidence that prover9 found a proof
        fileContainsProof( output_file )
      }
      case 3 => {
        throw new Prover9Exception( "The max_megs (memory limit) parameter was exceeded." )
      }
      case 4 => {
        throw new Prover9Exception( "The max_seconds parameter was exceeded." )
      }
      case 5 => {
        throw new Prover9Exception( "The max_given parameter was exceeded." )
      }
      case 6 => {
        throw new Prover9Exception( "The max_kept parameter was exceeded." )
      }
      case 7 => {
        throw new Prover9Exception( "A Prover9 action terminated the search." )
      }
      case 101 => throw new Prover9Exception( "Prover9 received an interrupt signal." )
      case 102 => throw new Prover9Exception( "Prover9 crashed, most probably due to a bug." )
    }
  }

  private def prove( seq: FSequent, input_file: String, output_file: String ): Option[RobinsonResolutionProof] =
    {
      val tmp_file = File.createTempFile( "gapt-prover9-proof", ".tptp", null )
      tmp_file.deleteOnExit()
      writeProofProblem( seq, tmp_file )

      tptpToLadr( tmp_file.getAbsolutePath, input_file )
      tmp_file.delete
      // also pass along a CNF of the negated sequent so that
      // the proof obtained by prover9 can be fixed to have
      // as the clauses the clauses of this CNF (and not e.g.
      // these clauses modulo symmetry)
      val cs = Some( CNFn( seq.toFormula ).map( _.toFSequent ).toList )
      runP9OnLADR( input_file, output_file, cs )
    }

  private def refuteNamed( named_sequents: List[Tuple2[String, FSequent]], input_file: String, output_file: String ): Option[RobinsonResolutionProof] =
    {
      val tmp_file = File.createTempFile( "gapt-prover9-ref", ".tptp", null )
      tmp_file.deleteOnExit()
      trace( "writing refutational problem" )
      writeRefutationProblem( named_sequents, tmp_file )
      trace( "converting tptp to ladr" )
      tptpToLadr( tmp_file.getAbsolutePath, input_file )
      tmp_file.delete
      runP9OnLADR( input_file, output_file, Some( named_sequents.map( p => p._2 ) ) )
    }

  private def runP9OnLADR( input_file: String, output_file: String, clauses: Option[Seq[FSequent]] = None ): Option[RobinsonResolutionProof] = {
    // find out which symbols have been renamed
    // this information should eventually be used when
    // parsing the prover9 proof
    val regexp = new Regex( """%\s*\(arity (\d+)\)\s*'(.*?)'\s*(ladr\d+)""" )

    val str_ladr = Source.fromInputStream( new FileInputStream( input_file ) ).mkString

    val symbol_map = str_ladr.split( System.getProperty( "line.separator" ) ).foldLeft( new HashMap[String, ( Int, String )] )( ( m, l ) =>
      l match {
        case regexp( arity, orig, repl ) => m.updated( repl, ( arity.toInt, orig ) )
        case _                           => m
      } )

    trace( "translation map: " )
    trace( symbol_map.toString )

    trace( "running prover9" )
    val ret = runP9( input_file, output_file )
    trace( "prover9 finished" )
    ret match {
      case 0 =>
        try {
          val p9proof = parse_prover9( output_file )
          val tp9proof = NameReplacement( p9proof._1, symbol_map )
          val ret = if ( clauses != None ) fixDerivation( tp9proof, clauses.get ) else tp9proof
          Some( ret )
        } catch {
          case e: Exception =>
            debug( "Prover9 run successfully but conversion to resolution proof failed! " + e.getMessage )
            val stackelements = e.getStackTrace
            for ( ste <- stackelements )
              trace( ste.getFileName + ":" + ste.getLineNumber + " " + ste.getClassName + "." + ste.getMethodName )
            Some( InitialClause( Nil, Nil ) )
        }
      case 1 => throw new Prover9Exception( "A fatal error occurred (user's syntax error or Prover9's bug)." )
      case 2 => {
        trace( "Prover9 ran out of things to do (sos list exhausted)." )
        // Sometimes, prover9 returns with this exit code even though
        // a proof has been found. Hack-ish solution: Try to parse, if
        // we fail, we assume that no proof was actually produced.
        //
        // FIXME: throw a specific exception in case no proof is found
        // and handle it here.
        // 
        try {
          trace( "parsing prover9 to robinson" )
          val p9proof = parse_prover9( output_file )
          trace( "done parsing prover9 to robinson" )
          trace( "doing name replacement" )
          val tp9proof = NameReplacement( p9proof._1, symbol_map )

          trace( "done doing name replacement" )
          val ret = if ( clauses != None ) fixDerivation( tp9proof, clauses.get ) else tp9proof
          trace( "done fixing symmetry" )
          Some( ret )
        } catch {
          case _: Exception => None // Prover9 ran out of things to do (sos list exhausted).
        }
      }
      case 3 => {
        trace( "The max_megs (memory limit) parameter was exceeded." )
        None // The max_megs (memory limit) parameter was exceeded.
      }
      case 4 => {
        trace( "The max_seconds parameter was exceeded." )
        None // The max_seconds parameter was exceeded.
      }
      case 5 => {
        trace( "The max_given parameter was exceeded." )
        None // The max_given parameter was exceeded.
      }
      case 6 => {
        trace( "The max_kept parameter was exceeded." )
        None // The max_kept parameter was exceeded.
      }
      case 7 => {
        trace( "A Prover9 action terminated the search." )
        None // A Prover9 action terminated the search.
      }
      case 101 => throw new Prover9Exception( "Prover9 received an interrupt signal." )
      case 102 => throw new Prover9Exception( "Prover9 crashed, most probably due to a bug." )
    }
  }

  private def refute( sequents: List[FSequent], input_file: String, output_file: String ): Option[RobinsonResolutionProof] =
    refuteNamed( sequents.zipWithIndex.map( p => ( "sequent" + p._2, p._1 ) ), input_file, output_file )

  /**
   * Proves a sequent through Prover9 (which refutes the corresponding set of clauses).
   */
  def prove( seq: FSequent ): Option[RobinsonResolutionProof] = {
    //val (gseq, map) = ground(seq)
    val in_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    in_file.deleteOnExit()
    out_file.deleteOnExit()
    val ret = prove( seq, in_file.getAbsolutePath, out_file.getAbsolutePath )
    //val ret = prove( gseq, in_file.getAbsolutePath, out_file.getAbsolutePath )
    //val ret2 = unground( ret.get, map )
    in_file.delete
    out_file.delete
    //ret2
    ret
  }

  /**
   * Refutes a set of clauses, given as a List[FSequent].
   */
  def refute( sequents: List[FSequent] ): Option[RobinsonResolutionProof] = {
    val in_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    in_file.deleteOnExit()
    out_file.deleteOnExit()
    val ret = refute( sequents, in_file.getAbsolutePath, out_file.getAbsolutePath )
    in_file.delete
    out_file.delete
    ret
  }

  def refute( filename: String ): Option[RobinsonResolutionProof] = {
    val out_file = File.createTempFile( "gapt-prover9", "prover9", null )
    out_file.deleteOnExit()
    val ret = runP9OnLADR( new File( filename ).getAbsolutePath, out_file.getAbsolutePath )
    out_file.delete
    ret
  }

  def refuteTPTP( fn: String ): Option[RobinsonResolutionProof] = {
    val out_file = File.createTempFile( "gapt-prover9", ".ladr", null )
    out_file.deleteOnExit()
    tptpToLadr( fn, out_file.getAbsolutePath )
    val proof = refute( out_file.getAbsolutePath )
    out_file.delete
    proof
  }

  /* Takes the output of prover9, extracts a resolution proof, the original endsequent and the clauses. */
  def parse_prover9( p9_file: String ): ( RobinsonResolutionProof, FSequent, FSequent ) = {

    val pt_file = File.createTempFile( "gapt-prover9", ".pt", null )
    pt_file.deleteOnExit()
    p9_to_p9( p9_file, pt_file.getCanonicalPath )
    val ivy_file = File.createTempFile( "gapt-prover9", ".ivy", null )
    ivy_file.deleteOnExit()
    p9_to_ivy( pt_file.getCanonicalPath, ivy_file.getCanonicalPath )

    val iproof = IvyParser( ivy_file.getCanonicalPath, IvyStyleVariables )
    val rproof = IvyToRobinson( iproof )

    //val mproof = InstantiateElimination(rproof)
    val mproof = rproof
    //val mproof = if (clauses != None) fixSymmetry(rproof, clauses.get) else rproof
    pt_file.delete
    ivy_file.delete

    //    val fs = Prover9TermParser.normalizeFSequent(InferenceExtractor(p9_file))

    val fs = InferenceExtractor.viaLADR( p9_file )
    val clauses = InferenceExtractor.clausesViaLADR( p9_file )
    //println("extracted formula: "+fs)
    ( mproof, fs, clauses )
  }

  def parse_prover9LK( p9_file: String, forceSkolemization: Boolean = false ): LKProof = {

    val ( proof, endsequent, clauses ) = Prover9.parse_prover9( p9_file )
    //val sendsequent = skolemize(endsequent)
    //val folsendsequent= FSequent(sendsequent.antecedent.map(x => hol2fol(x)), sendsequent.succedent.map(x => hol2fol(x)))

    if ( !forceSkolemization && !containsStrongQuantifier( endsequent ) ) {

      val ant = endsequent.antecedent.map( x => univclosure( x.asInstanceOf[FOLFormula] ) )
      val suc = endsequent.succedent.map( x => existsclosure( x.asInstanceOf[FOLFormula] ) )
      val closure = FSequent( ant, suc )

      val clause_set = CNFn( endsequent.toFormula ).map( c =>
        FSequent( c.neg.map( f => f.asInstanceOf[FOLFormula] ), c.pos.map( f => f.asInstanceOf[FOLFormula] ) ) )

      val res_proof = fixDerivation( proof, clause_set )
      //println("res_proof: "+res_proof)

      RobinsonToLK( res_proof, closure )

    } else {

      val fclauses: Set[FClause] = proof.nodes.map {
        case InitialClause( clause ) => clause.toFClause
        case _                       => FClause( Nil, Nil )
      } filter ( ( x: FClause ) => x match {
        case FClause( Nil, Nil ) => false;
        case _                   => true
      } )
      val clauses = fclauses.map( c => univclosure( FOLOr(
        c.neg.map( f => FOLNeg( f.asInstanceOf[FOLFormula] ) ).toList ++
          c.pos.map( f => f.asInstanceOf[FOLFormula] ).toList ) ) )
      val clauses_ = clauses.partition( _ match {
        case FOLNeg( _ ) => false;
        case _           => true
      } )
      //val cendsequent = FSequent(clauses.toList, Nil)
      val cendsequent2 = FSequent( clauses_._1.toList, clauses_._2.map( _ match {
        case FOLNeg( x ) => x
      } ).toList )

      RobinsonToLK( proof, cendsequent2 )

    }
  }

  val isInstalled: Boolean = {
    if ( !isLadrToTptpInstalled() ) {
      warn( "ladr_to_tptp not found!" )
      false
    }
    else if ( !isProver9Installed() ) {
      warn( "prover9 not found!" )
      false
    }
    else if ( !isProoftransInstalled() ) {
      warn( "prooftrans not found!" )
      false
    }
    else if ( !isTptpToLadrInstalled() ) {
      warn( "tptp_to_ladr not found!" )
      false
    }
    else true
  }

  private def isLadrToTptpInstalled(): Boolean = callBinary( "ladr_to_tptp" ) == 1
  private def isTptpToLadrInstalled(): Boolean = callBinary( "tptp_to_ladr" ) == 0
  private def isProver9Installed(): Boolean = callBinary( "prover9" ) == 2
  private def isProoftransInstalled(): Boolean = callBinary( "prooftrans" ) == 1

  private def callBinary( name: String ): Int = {
    val err = StringBuilder.newBuilder
    val out = StringBuilder.newBuilder
    val logger = ProcessLogger( line => out ++= line, line => err ++= line )
    try {
      val pio = name run logger
      pio.exitValue()
    } catch {
      case e: Exception =>
        -1
    }
  }

}

class Prover9Prover extends Prover with at.logic.gapt.utils.logging.Logger {
  def getRobinsonProof( seq: FSequent ) = Prover9.prove( seq )

  /**
   * Return an LK proof of seq.
   *
   * Note: We interpret free variables as constants. This
   * makes sense from the proof point-of-view (as opposed to
   * the refutational point-of-view).
   * If we don't do this, prover9 substitutes for the variables
   * in the formula (i.e. it proves the existential closure, not
   * the universal closure, as expected).
   *
   * TODO: the ground/unground code should be in Prover9.prove, and
   * the replacement applied to the resolution proof already (not the
   * LK proof, as we do it here.) To do this, a applyReplacement for
   * resolution proofs needs to be written.
   */
  def getLKProof( seq: FSequent ): Option[LKProof] =
    {
      val ( gseq, map ) = ground( seq )

      getRobinsonProof( gseq ) match {
        case Some( proof ) => {
          trace( " got a robinson proof from prover9, translating " )
          Some( unground( RobinsonToLK( proof, gseq ), map ) )
        }
        case None => {
          trace( " proving with prover9 failed " )
          None
        }
      }
    }

  // Grounds a sequent by replacing variables by new constants.
  private def ground( seq: FSequent ): ( FSequent, Map[FOLVar, FOLConst] ) = {
    // FIXME: cast of formula of sequent!
    val free = seq.antecedent.flatMap(
      f => freeVariables( f.asInstanceOf[FOLFormula] ) ).toSet ++
      seq.succedent.flatMap( f => freeVariables( f.asInstanceOf[FOLFormula] ) ).toSet
    // FIXME: make a better association between the consts and the vars.
    //val map = free.zip( free.map( v => new FOLConst( new CopySymbol( v.name ) ) ) ).toMap
    val map = free.zip( free.map( v => new FOLConst( v.sym ) ) ).toMap
    trace( "grounding map in prover9: " )
    trace( map.toString )
    // FIXME: cast of formula of sequent!
    val subst = FOLSubstitution( map )
    val ret = FSequent( seq.antecedent.map( f => subst( f.asInstanceOf[FOLFormula] ) ),
      seq.succedent.map( f => subst( f.asInstanceOf[FOLFormula] ) ) )
    ( ret, map )
  }

  private def unground( p: LKProof, map: Map[FOLVar, FOLConst] ) =
    applyReplacement( p, map.map( x => x.swap ) )._1

  /* TODO: should use this when grounding instead of ConstantStringSymbol
           to avoid name clashes. Can't seem to get equality to work,
           though.

  case class CopySymbol( val s: SymbolA ) extends ConstantSymbolA {
    override def toString() = s.toString
    def toCode() = "CopySymbol( " + s.toCode + " )"
    def compare(that: SymbolA) = that match {
      case CopySymbol( s2 ) => s.compare( s2 )
    }
    override def unique = "CopySymbol" 
  }
*/

  override def isValid( seq: FSequent ): Boolean = Prover9.isValid( seq )
}
