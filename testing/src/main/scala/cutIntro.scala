package at.logic.gapt.testing

import at.logic.gapt.expr.{ EqC, constants }
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import java.io._
import java.nio.file.{ Paths, Files }
import at.logic.gapt.examples._
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.lk.base.{ LKRuleCreationException, LKProof }
import at.logic.gapt.proofs.lk.{ LKToExpansionProof, rulesNumber, containsEqualityReasoning }
import at.logic.gapt.proofs.lk.cutIntroduction._
import at.logic.gapt.proofs.resolution.{ numberOfResolutionsAndParamodulations, RobinsonToExpansionProof }
import at.logic.gapt.provers.maxsat.OpenWBO
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.logging.{ metrics, CollectMetrics }

import scala.io.Source
import scala.collection.immutable.HashMap

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.proofs.expansionTrees.{ addSymmetry, toShallow, ExpansionSequent }

import org.json4s._
import org.json4s.native.JsonMethods._

import scala.concurrent.duration._

object testCutIntro extends App {

  val resultsOut = new PrintWriter( "result_lines.json" )

  val timeOut = 60 seconds
  val veritTimeOut = 5 minutes

  compressAll()

  resultsOut.close()

  Files.write(
    Paths.get( "results.json" ),
    compact( render( JArray(
      Source.fromFile( "result_lines.json" ).getLines().map( parse( _ ) ).toList
    ) ) ).getBytes
  )

  def compressAll() {
    compressAll( DeltaTableMethod( false ) )
    compressAll( DeltaTableMethod( true ) )

    val solver = new OpenWBO
    compressAll( MaxSATMethod( solver, 1 ) )
    compressAll( MaxSATMethod( solver, 1, 1 ) )
    compressAll( MaxSATMethod( solver, 2 ) )
    compressAll( MaxSATMethod( solver, 2, 2 ) )
  }

  def compressAll( method: GrammarFindingMethod ) = {
    compressProofSequences( method )
    compressTSTP( "testing/resultsCutIntro/tstp_non_trivial_termset.csv", method )
    compressLeanCoP( method )
    compressVeriT( "testing/veriT-SMT-LIB/QF_UF/", method )
  }

  def saveMetrics( timeout: Duration )( f: => Unit ): CollectMetrics = {
    val collectedMetrics = new CollectMetrics
    metrics.current.withValue( collectedMetrics ) {
      try {
        withTimeout( timeout ) {
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

    def jsonify( v: Any ): JValue = v match {
      case l: Long    => JInt( l )
      case l: Int     => JInt( l )
      case b: Boolean => JBool( b )
      case l: Seq[_]  => JArray( l map jsonify toList )
      case s          => JString( s toString )
    }

    val json = JObject( collectedMetrics.data mapValues jsonify toList )
    resultsOut.println( compact( render( json ) ) ); resultsOut.flush()

    collectedMetrics
  }

  def compressLKProof( p: LKProof, method: GrammarFindingMethod ) = {
    val hasEquality = containsEqualityReasoning( p )
    metrics.value( "lkinf_input", rulesNumber( p ) )
    compressExpansionProof( LKToExpansionProof( p ), hasEquality, method )
  }

  def compressExpansionProof( ep: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod ) = {
    metrics.value( "method", method.name )
    metrics.value( "has_equality", hasEquality )
    CutIntroduction.compressToLK( ep, hasEquality, method, verbose = false ) match {
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
  def compressTSTP( str: String, method: GrammarFindingMethod ) = {

    // Process each file in parallel
    Source.fromFile( str ).getLines() foreach { l =>
      val data = l.split( "," )
      saveMetrics( timeOut ) { compressTSTPProof( data( 0 ), method ) }
    }
  }

  /// compress the prover9-TSTP proof found in file fn
  def compressTSTPProof( fn: String, method: GrammarFindingMethod ) = {
    metrics.value( "file", fn )
    wrapParse { Some( Prover9Importer.robinsonProofWithReconstructedEndSequentFromFile( fn ) ) } foreach {
      case ( resProof, endSequent ) =>
        metrics.value( "resinf_input", numberOfResolutionsAndParamodulations( resProof ) )
        val expansionProof = RobinsonToExpansionProof( resProof, endSequent )
        val containsEquations = constants( toShallow( expansionProof ) ) exists {
          case EqC( _ ) => true
          case _        => false
        }
        compressExpansionProof( expansionProof, containsEquations, method )
    }
  }

  /****************************** VeriT SMT-LIB ******************************/

  // Compress all veriT-proofs found in the directory str and beyond
  def compressVeriT( str: String, method: GrammarFindingMethod ) = {
    getVeriTProofs( str ) foreach { p =>
      saveMetrics( veritTimeOut ) { compressVeriTProof( p, method ) }
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
  def compressVeriTProof( str: String, method: GrammarFindingMethod ) {
    metrics.value( "file", str )

    wrapParse { VeriTParser.getExpansionProof( str ) } foreach { ep =>
      // VeriT proofs have the equality axioms as formulas in the end-sequent
      compressExpansionProof( addSymmetry( ep ), hasEquality = false, method )
    }
  }

  // leancop

  def compressLeanCoP( method: GrammarFindingMethod ) = {
    recursiveListFiles( "testing/TSTP/leanCoP" ) foreach { f =>
      if ( f.getName endsWith ".out" ) {
        compressLeanCoPProof( f.getPath, method )
      }
    }
  }

  def compressLeanCoPProof( fn: String, method: GrammarFindingMethod ) = saveMetrics( timeOut ) {
    metrics.value( "file", fn )
    wrapParse { LeanCoPParser.getExpansionProof( fn ) } foreach { proof =>
      compressExpansionProof( proof, true, method )
    }
  }

  /***************************** Proof Sequences ******************************/

  def compressProofSequences( method: GrammarFindingMethod ) = {
    proofSequences foreach { proofSeq =>
      var i = 0
      var status = ""
      while ( !status.endsWith( "timeout" ) ) {
        i = i + 1
        val pn = s"${proofSeq.name}($i)"
        status = saveMetrics( timeOut ) {
          metrics.value( "file", pn )
          compressLKProof( proofSeq( i ), method )
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
      println( file )
      total += 1
      try {
        withTimeout( timeout seconds ) {
          val p = Prover9Importer.expansionProofFromFile( file.getAbsolutePath )
          try {
            val ts = TermsExtraction( p )
            val tssize = ts.set.size
            val n_functions = ts.formulas.distinct.size

            if ( tssize > n_functions )
              termsets += ( file.getAbsolutePath -> ts )
            else num_trivial_termset += 1
          } catch {
            case e: Throwable => error_term_extraction += 1
          }
        }
      } catch {
        case e: Throwable => error_parser += 1
      }
    }
  }

}
