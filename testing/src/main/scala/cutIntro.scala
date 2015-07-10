package at.logic.gapt.testing

import java.io._
import java.nio.file.{ Paths, Files }
import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.{ loadVeriTProof, extractTerms, loadProver9LKProof }
import at.logic.gapt.examples._
import at.logic.gapt.proofs.lk.base.{ LKRuleCreationException, LKProof }
import at.logic.gapt.proofs.lk.cutIntroduction._
import at.logic.gapt.utils.logging.{ metrics, CollectMetrics }

import scala.io.Source
import scala.collection.immutable.HashMap
import org.slf4j.LoggerFactory

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent

import org.json4s._
import org.json4s.native._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._

import scala.concurrent.duration._

/**
 * ********
 * test script for the cut-introduction algorithm on output proofs from prover9,
 * veriT and example proof sequences.
 * usage example from CLI:
 *
 * scala> :load testing/testCutIntro.scala
 *
 * scala> testCutIntro.findNonTrivialTSTPExamples( "testing/TSTP/prover9/", 60 )
 *
 * test the tests by
 * scala> testCutIntro.compressTSTP ("testing/resultsCutIntro/tstp_minitest.csv", timeout: Int, method: Int)
 * scala> testCutIntro.compressVeriT ("testing/veriT-SMT-LIB/QF_UF/eq_diamond/", timeout: Int, method: Int)
 * scala> testCutIntro.compressProofSequences (timeout: Int, method: Int)
 * Where method is:
 * 0: introduce one cut with one quantifier
 * 1: introduce one cut with as many quantifiers as possible
 * 2: introduce many cuts with one quantifier each
 *
 * run the tests by
 * scala> testCutIntro.compressAll(timeout: Int)
 * see compressAll for how to call specific tests
 * ********
 */

object testCutIntro extends App {

  val resultsOut = new PrintWriter( "result_lines.json" )

  compressAll( 60 )

  resultsOut.close()

  Files.write( Paths.get( "results.json" ),
    compact( render( JArray(
      Source.fromFile( "result_lines.json" ).getLines().map( parse( _ ) ).toList ) ) ).getBytes )

  def apply() = {
    println( "Usage: for example calls please see the implementation of testCutIntro.compressAll()" )
  }

  def compressAll( timeout: Int ) {
    compressAll( DeltaTableMethod( false ), timeout )
    compressAll( DeltaTableMethod( true ), timeout )
    compressAll( MaxSATMethod( 1 ), timeout )
    compressAll( MaxSATMethod( 2 ), timeout )
    compressAll( MaxSATMethod( 2, 2 ), timeout )
  }

  def compressAll( method: GrammarFindingMethod, timeout: Int ) = {
    compressProofSequences( timeout, method )
    compressTSTP( "testing/resultsCutIntro/tstp_non_trivial_termset.csv", timeout, method )
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
          metrics.value( "status", collectedMetrics.currentPhase + "_timeout" )
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
    }

    val json = JObject( collectedMetrics.data.mapValues {
      case l: Long => JInt( l )
      case l: Int  => JInt( l )
      case s       => JString( s toString )
    }.toList )
    resultsOut.println( compact( render( json ) ) ); resultsOut.flush()

    collectedMetrics
  }

  /*
   * Everything eventually ends up in one of these two methods.
   * All calls to cut-introduction and logging are done exclusively here
   *
   */
  def compressLKProof( proof: Option[LKProof], timeout: Int, method: GrammarFindingMethod ) = {
    metrics.value( "method", method.name )
    CutIntroduction.execute( proof.get, method ) match {
      case Some( _ ) => metrics.value( "status", "ok" )
      case None      => metrics.value( "status", "cutintro_uncompressible" )
    }
  }

  def compressExpansionProof( ep: Option[ExpansionSequent], hasEquality: Boolean, timeout: Int, method: GrammarFindingMethod ) = {
    metrics.value( "method", method.name )
    CutIntroduction.execute( ep.get, hasEquality, method ) match {
      case Some( _ ) => metrics.value( "status", "ok" )
      case None      => metrics.value( "status", "cutintro_uncompressible" )
    }
  }

  /************** finding non-trival prover9-TSTP proofs **********************/

  var total = 0
  var num_trivial_termset = 0
  var error_parser = 0
  var error_term_extraction = 0
  // Hashmap containing proofs with non-trivial termsets
  var termsets = HashMap[String, TermSet]()

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

    var instance_per_formula = 0.0
    var ts_size = 0
    val data = termsets.foldLeft( "" ) {
      case ( acc, ( k, v ) ) =>
        val tssize = v.set.size
        val n_functions = v.formulas.distinct.size
        instance_per_formula += tssize.toFloat / n_functions.toFloat
        ts_size += tssize
        k + "," + n_functions + "," + tssize + "\n" + acc
    }

    val avg_inst_per_form = instance_per_formula / termsets.size
    val avg_ts_size = ts_size.toFloat / termsets.size.toFloat

    bw.write( data )
    bw.close()

    bw_s.write( "Total number of proofs: " + total + "\n" )
    bw_s.write( "Total number of proofs with trivial termsets: " + num_trivial_termset + "\n" )
    bw_s.write( "Total number of proofs with non-trivial termsets: " + termsets.size + "\n" )
    bw_s.write( "Time limit exceeded or exception during parsing: " + error_parser + "\n" )
    bw_s.write( "Time limit exceeded or exception during terms extraction: " + error_term_extraction + "\n" )
    bw_s.write( "Average instances per quantified formula: " + avg_inst_per_form + "\n" )
    bw_s.write( "Average termset size: " + avg_ts_size + "\n" )
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

  // Compress the prover9-TSTP proofs whose names are in the csv-file passed as parameter str
  def compressTSTP( str: String, timeout: Int, method: GrammarFindingMethod ) = {

    // Process each file in parallel
    val lines = Source.fromFile( str ).getLines().toList
    //lines.par.foreach { case l =>
    lines.foreach {
      case l =>
        val data = l.split( "," )
        saveMetrics( timeout ) { compressTSTPProof( data( 0 ), timeout, method ) }
    }
  }

  /// compress the prover9-TSTP proof found in file fn
  def compressTSTPProof( fn: String, timeout: Int, method: GrammarFindingMethod ) = {
    metrics.value( "file", fn )
    if ( fn.endsWith( ".out" ) ) {
      try {
        val p = loadProver9LKProof( fn )
        compressLKProof( Some( p ), timeout, method )
      } catch {
        case e: TimeOutException =>
          metrics.value( "status", "parsing_timeout" )
        case e: OutOfMemoryError =>
          metrics.value( "status", "parsing_out_of_memory" )
        case e: StackOverflowError =>
          metrics.value( "status", "parsing_stack_overflow" )
        case e: Exception =>
          metrics.value( "status", "parsing_other_exception" )
      }
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

    try {
      loadVeriTProof( str ) map { ep =>
        // VeriT proofs have the equality axioms as formulas in the end-sequent
        compressExpansionProof( Some( ep ), false, timeout, method )
      } getOrElse {
        metrics.value( "status", "parsing_no_proof_found" )
      }
    } catch {
      case e: TimeOutException =>
        metrics.value( "status", "parsing_timeout" )
      case e: OutOfMemoryError =>
        metrics.value( "status", "parsing_out_of_memory" )
      case e: StackOverflowError =>
        metrics.value( "status", "parsing_stack_overflow" )
      case e: Exception =>
        metrics.value( "status", "parsing_other_exception" )
    }
  }

  /***************************** Proof Sequences ******************************/

  def compressProofSequences( timeout: Int, method: GrammarFindingMethod ) = {

    def compress( p: LKProof, pn: String ): String =
      saveMetrics( timeout ) {
        metrics.value( "file", pn )
        compressLKProof( Some( p ), timeout, method )
      }.data( "status" ).toString

    var i = 0
    var status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "LinearExampleProof(" + i + ")"
      status = compress( LinearExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "SquareDiagonalExampleProof(" + i + ")"
      status = compress( SquareDiagonalExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "SquareEdgesExampleProof(" + i + ")"
      status = compress( SquareEdgesExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "SquareEdges2DimExampleProof(" + i + ")"
      status = compress( SquareEdges2DimExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "LinearEqExampleProof(" + i + ")"
      status = compress( LinearEqExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "SumOfOnesF2ExampleProof(" + i + ")"
      status = compress( SumOfOnesF2ExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "SumOfOnesFExampleProof(" + i + ")"
      status = compress( SumOfOnesFExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "SumOfOnesExampleProof(" + i + ")"
      status = compress( SumOfOnesExampleProof( i ), pn )
    }

    i = 0
    status = ""
    while ( !status.endsWith( "timeout" ) ) {
      i = i + 1
      val pn = "UniformAssociativity3ExampleProof(" + i + ")"
      status = compress( UniformAssociativity3ExampleProof( i ), pn )
    }
  }

  /*
  def compressLKProof( name: String, p: LKProof, timeout: Int, moduloEq: Boolean, useForgetfulPara: Boolean ) = {
    val r = if ( moduloEq )
      compressExpansionProof( removeEqAxioms( extractExpansionTrees( p )), new EquationalProver(), timeout, useForgetfulPara )
    else
      compressExpansionProof( extractExpansionTrees( p ), new DefaultProver(), timeout, false )

    val status = r._1
    val cutintro_logline = r._2

    CutIntroDataLogger.trace( name + ",n/a," + status + ",n/a," + rulesNumber( p ) + "," + quantRulesNumber( p ) + cutintro_logline ) // log all, computing #infqf, #qinfcf
  }

  def removeEqAxioms( eseq: ExpansionSequent ) = {
   // removes all equality axioms that appear in examples/ProofSequences.scala
   val R = parse.fol( "Forall x =(x,x)" )
   val S = parse.fol( "Forall x Forall y Imp =(x,y) =(y,x)" )
   val T = parse.fol( "Forall x Forall y Forall z Imp And =(x,y) =(y,z) =(x,z)" )
   val Tprime = parse.fol( "Forall x Forall y Forall z Imp =(x,y) Imp =(y,z) =(x,z)" )
   val CSuc = parse.fol( "Forall x Forall y Imp =(x,y) =(s(x),s(y))" )
   val CPlus = parse.fol( "Forall x Forall y Forall u Forall v Imp =(x,y) Imp =(u,v) =(+(x,u),+(y,v))" )
   val CPlusL = parse.fol( "Forall x Forall y Forall z Imp =(y,z) =(+(y,x),+(z,x))" ) // congruence plus left
   val CgR = parse.fol( "Forall x Forall y Forall z Imp =(y,z) =(g(x,y),g(x,z))" ) // congruence of g on the right
   val CMultR = parse.fol( "Forall x Forall y Forall z Imp =(x,y) =(*(z,x),*(z,y))" ) // congruence of mult right

   val eqaxioms = new FSequent( R::S::T::Tprime::CSuc::CPlus::CPlusL::CgR::CMultR::Nil, Nil )
   
   removeFromExpansionSequent( eseq, eqaxioms )
  }
*/

}

object findNonTrivialTSTPExamples extends App {
  testCutIntro.findNonTrivialTSTPExamples( "testing/TSTP/prover9", 60 )
}