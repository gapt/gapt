package at.logic.gapt.testing

import at.logic.gapt.formats.leanCoP.LeanCoPParser
import java.io._
import java.nio.file.{ Paths, Files }
import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.{ loadVeriTProof, extractTerms, loadProver9LKProof }
import at.logic.gapt.examples._
import at.logic.gapt.proofs.lk.base.{ LKRuleCreationException, LKProof }
import at.logic.gapt.proofs.lk.cutIntroduction._
import at.logic.gapt.utils.logging.{ metrics, CollectMetrics }

import scala.io.Source
import scala.collection.immutable.HashMap

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent

import org.json4s._
import org.json4s.native.JsonMethods._

import scala.concurrent.duration._

object testCutIntro extends App {

  val resultsOut = new PrintWriter( "result_lines.json" )

  compressAll( 60 )

  resultsOut.close()

  Files.write(
    Paths.get( "results.json" ),
    compact( render( JArray(
      Source.fromFile( "result_lines.json" ).getLines().map( parse( _ ) ).toList
    ) ) ).getBytes
  )

  def compressAll( timeout: Int ) {
    compressAll( DeltaTableMethod( false ), timeout )
    compressAll( DeltaTableMethod( true ), timeout )
    compressAll( MaxSATMethod( 1 ), timeout )
    compressAll( MaxSATMethod( 1, 1 ), timeout )
    compressAll( MaxSATMethod( 2 ), timeout )
    compressAll( MaxSATMethod( 2, 2 ), timeout )
  }

  def compressAll( method: GrammarFindingMethod, timeout: Int ) = {
    compressProofSequences( timeout, method )
    compressTSTP( "testing/resultsCutIntro/tstp_non_trivial_termset.csv", timeout, method )
    compressLeanCoP( timeout, method )
    compressVeriT( "testing/veriT-SMT-LIB/QF_UF/", timeout * 5, method )
  }

  def saveMetrics( timeout: Int )( f: => Unit ): CollectMetrics = {
    val collectedMetrics = new CollectMetrics
    metrics.current.withValue( collectedMetrics ) {
      try {
        withTimeout( timeout seconds ) {
          metrics.time( "total" )( f )
        }
      } catch {
        case e: TimeOutException =>
          metrics.value( "status", "cutintro_timeout" )
        case e: OutOfMemoryError =>
          metrics.value( "status", "cutintro_out_of_memory" )
        case e: StackOverflowError =>
          metrics.value( "status", "cutintro_stack_overflow" )
        case e: CutIntroEHSUnprovableException =>
          metrics.value( "status", "cutintro_ehs_unprovable" )
        case e: LKRuleCreationException =>
          metrics.value( "status", "lk_rule_creation_exception" )
        case e: Throwable =>
          metrics.value( "status", "cutintro_other_exception" )
      }
      metrics.value( "phase", collectedMetrics.currentPhase )
    }

    val json = JObject( collectedMetrics.data.mapValues {
      case l: Long => JInt( l )
      case l: Int  => JInt( l )
      case s       => JString( s toString )
    }.toList )
    resultsOut.println( compact( render( json ) ) ); resultsOut.flush()

    collectedMetrics
  }

  def compressLKProof( proof: LKProof, timeout: Int, method: GrammarFindingMethod ) = {
    metrics.value( "method", method.name )
    CutIntroduction.execute( proof, method ) match {
      case Some( _ ) => metrics.value( "status", "ok" )
      case None      => metrics.value( "status", "cutintro_uncompressible" )
    }
  }

  def compressExpansionProof( ep: ExpansionSequent, hasEquality: Boolean, timeout: Int, method: GrammarFindingMethod ) = {
    metrics.value( "method", method.name )
    CutIntroduction.execute( ep, hasEquality, method ) match {
      case Some( _ ) => metrics.value( "status", "ok" )
      case None      => metrics.value( "status", "cutintro_uncompressible" )
    }
  }

  def wrapParse[T]( thunk: => Option[T] ): Option[T] = {
    try {
      thunk orElse {
        metrics.value( "status", "parsing_no_proof_found" )
        None
      }
    } catch {
      case e: ThreadDeath =>
        metrics.value( "status", "parsing_timeout" )
        None
      case e: OutOfMemoryError =>
        metrics.value( "status", "parsing_out_of_memory" )
        None
      case e: StackOverflowError =>
        metrics.value( "status", "parsing_stack_overflow" )
        None
      case e: Exception =>
        metrics.value( "status", "parsing_other_exception" )
        None
    }
  }

  // Compress the prover9-TSTP proofs whose names are in the csv-file passed as parameter str
  def compressTSTP( str: String, timeout: Int, method: GrammarFindingMethod ) = {

    // Process each file in parallel
    Source.fromFile( str ).getLines() foreach { l =>
      val data = l.split( "," )
      saveMetrics( timeout ) { compressTSTPProof( data( 0 ), timeout, method ) }
    }
  }

  /// compress the prover9-TSTP proof found in file fn
  def compressTSTPProof( fn: String, timeout: Int, method: GrammarFindingMethod ) = {
    metrics.value( "file", fn )
    wrapParse { Some( loadProver9LKProof( fn ) ) } foreach { p =>
      compressLKProof( p, timeout, method )
    }
  }

  /****************************** VeriT SMT-LIB ******************************/

  // Compress all veriT-proofs found in the directory str and beyond
  def compressVeriT( str: String, timeout: Int, method: GrammarFindingMethod ) = {
    getVeriTProofs( str ) foreach { p =>
      saveMetrics( timeout ) { compressVeriTProof( p, timeout, method ) }
    }
  }

  def getVeriTProofs( str: String ): List[String] = {
    val file = new File( str )
    if ( file.isDirectory ) {
      val children = file.listFiles
      children.foldLeft( List[String]() )( ( acc, f ) => acc ::: getVeriTProofs( f.getPath ) )
    } else if ( file.getName.endsWith( ".proof_flat" ) ) {
      List( file.getPath )
    } else List()
  }

  // Compress the veriT-proof in file str
  def compressVeriTProof( str: String, timeout: Int, method: GrammarFindingMethod ) {
    metrics.value( "file", str )

    wrapParse { loadVeriTProof( str ) } foreach { ep =>
      // VeriT proofs have the equality axioms as formulas in the end-sequent
      compressExpansionProof( ep, false, timeout, method )
    }
  }

  // leancop

  def compressLeanCoP( timeout: Int, method: GrammarFindingMethod ) = {
    recursiveListFiles( "testing/TSTP/leanCoP" ) foreach { f =>
      if ( f.getName endsWith ".out" ) {
        compressLeanCoPProof( f.getPath, timeout, method )
      }
    }
  }

  def compressLeanCoPProof( fn: String, timeout: Int, method: GrammarFindingMethod ) = saveMetrics( timeout ) {
    metrics.value( "file", fn )
    wrapParse { LeanCoPParser.getExpansionProof( fn ) } foreach { proof =>
      compressExpansionProof( proof, true, timeout, method )
    }
  }

  /***************************** Proof Sequences ******************************/

  def compressProofSequences( timeout: Int, method: GrammarFindingMethod ) = {
    proofSequences foreach { proofSeq =>
      var i = 0
      var status = ""
      while ( !status.endsWith( "timeout" ) ) {
        i = i + 1
        val pn = s"${proofSeq.name}($i)"
        status = saveMetrics( timeout ) {
          metrics.value( "file", pn )
          compressLKProof( proofSeq( i ), timeout, method )
        }.data( "status" ).toString
      }
    }
  }
}

object findNonTrivialTSTPExamples extends App {
  var total = 0
  var num_trivial_termset = 0
  var error_parser = 0
  var error_term_extraction = 0
  // Hashmap containing proofs with non-trivial termsets
  var termsets = HashMap[String, TermSet]()

  findNonTrivialTSTPExamples( "testing/TSTP/prover9", 60 )

  def findNonTrivialTSTPExamples( str: String, timeout: Int ) = {

    nonTrivialTermset( str, timeout )
    val file = new File( "testing/resultsCutIntro/tstp_non_trivial_termset.csv" )
    val summary = new File( "testing/resultsCutIntro/tstp_non_trivial_summary.txt" )
    file.createNewFile()
    summary.createNewFile()
    val fw = new FileWriter( file.getAbsoluteFile )
    val bw = new BufferedWriter( fw )
    val fw_s = new FileWriter( summary.getAbsoluteFile )
    val bw_s = new BufferedWriter( fw_s )

    val nLine = sys.props( "line.separator" )

    var instance_per_formula = 0.0
    var ts_size = 0
    val data = termsets.foldLeft( "" ) {
      case ( acc, ( k, v ) ) =>
        val tssize = v.set.size
        val n_functions = v.formulas.distinct.size
        instance_per_formula += tssize.toFloat / n_functions.toFloat
        ts_size += tssize
        k + "," + n_functions + "," + tssize + nLine + acc
    }

    val avg_inst_per_form = instance_per_formula / termsets.size
    val avg_ts_size = ts_size.toFloat / termsets.size.toFloat

    bw.write( data )
    bw.close()

    bw_s.write( "Total number of proofs: " + total + nLine )
    bw_s.write( "Total number of proofs with trivial termsets: " + num_trivial_termset + nLine )
    bw_s.write( "Total number of proofs with non-trivial termsets: " + termsets.size + nLine )
    bw_s.write( "Time limit exceeded or exception during parsing: " + error_parser + nLine )
    bw_s.write( "Time limit exceeded or exception during terms extraction: " + error_term_extraction + nLine )
    bw_s.write( "Average instances per quantified formula: " + avg_inst_per_form + nLine )
    bw_s.write( "Average termset size: " + avg_ts_size + nLine )
    bw_s.close()

  }
  def nonTrivialTermset( str: String, timeout: Int ): Unit = {
    val file = new File( str )
    if ( file.isDirectory ) {
      val children = file.listFiles
      children.foreach( f => nonTrivialTermset( f.getAbsolutePath, timeout ) )
    } else if ( file.getName.endsWith( ".out" ) ) {
      total += 1
      try {
        withTimeout( timeout * 1000 ) {
          loadProver9LKProof( file.getAbsolutePath ) match {
            case p: LKProof => try {
              withTimeout( timeout * 1000 ) {
                val ts = extractTerms( p )
                val tssize = ts.set.size
                val n_functions = ts.formulas.distinct.size

                if ( tssize > n_functions )
                  termsets += ( file.getAbsolutePath -> ts )
                else num_trivial_termset += 1

              }
            } catch {
              case e: Throwable => error_term_extraction += 1
            }

          }
        }
      } catch {
        case e: Throwable => error_parser += 1
      }
    }
  }

}
