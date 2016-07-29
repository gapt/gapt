package at.logic.gapt.testing

import java.io.PrintWriter

import at.logic.gapt.cutintro._
import at.logic.gapt.examples._
import at.logic.gapt.expr.FOLFunction
import at.logic.gapt.grammars.DeltaTableMethod
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.loadExpansionProof
import at.logic.gapt.provers.maxsat.OpenWBO
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.logging.{ MetricsCollector, metrics }
import at.logic.gapt.utils.withTimeout
import org.json4s._
import org.json4s.native.JsonMethods._

import scala.collection.mutable
import scala.concurrent.duration._
import scala.util.{ Failure, Success }
import better.files._

class MetricsPrinter extends MetricsCollector {
  val data = mutable.Map[String, Any]()

  def jsonify( v: Any ): JValue = v match {
    case l: Long    => JInt( l )
    case l: Int     => JInt( l )
    case l: BigInt  => JInt( l )
    case l: Double  => JDouble( l )
    case l: Float   => JDouble( l )
    case b: Boolean => JBool( b )
    case l: Seq[_]  => JArray( l map jsonify toList )
    case s          => JString( s toString )
  }

  override def time[T]( phase: String )( f: => T ): T = {
    value( "phase", phase )

    val beginTime = System.currentTimeMillis()
    val result = f
    val endTime = System.currentTimeMillis()

    value( s"time_$phase", endTime - beginTime )

    result
  }

  override def value( key: String, value: => Any ) = {
    data( key ) = value
    println( s"METRICS ${compact( render( JObject( key -> jsonify( data( key ) ) ) ) )}" )
  }
}

object parseMethod {

  def apply( methodName: String ) = methodName match {
    case "1_dtable"       => DeltaTableMethod( singleQuantifier = true, subsumedRowMerging = false, keyLimit = None )
    case "many_dtable"    => DeltaTableMethod( singleQuantifier = false, subsumedRowMerging = false, keyLimit = None )
    case "many_dtable_ss" => DeltaTableMethod( singleQuantifier = false, subsumedRowMerging = true, keyLimit = None )

    case "reforest"       => ReforestMethod

    case _ if methodName endsWith "_maxsat" =>
      val vectorSizes = methodName.dropRight( "_maxsat".length ).split( "_" ).map( _.toInt )
      MaxSATMethod( OpenWBO, vectorSizes: _* )
  }

}

object testCutIntro extends App {

  val Array( fileName: String, methodName: String ) = args

  val metricsPrinter = new MetricsPrinter
  metrics.current.value = metricsPrinter
  metrics.value( "file", fileName )
  metrics.value( "method", methodName )

  val proofSeqRegex = """(\w+)\((\d+)\)""".r
  def loadProofForCutIntro( fileName: String ) = fileName match {
    case proofSeqRegex( name, n ) =>
      val p = proofSequences.find( _.name == name ).get( n.toInt )
      metrics.value( "lkinf_input", rulesNumber( p ) )
      Some( eliminateCutsET( LKToExpansionProof( p ) ) -> CutIntroduction.guessBackgroundTheory( p ) )
    case _ =>
      loadExpansionProof.withBackgroundTheory( fileName )
  }

  metrics.time( "total" ) {
    val parseResult = try metrics.time( "parse" ) {
      loadProofForCutIntro( fileName ) orElse {
        metrics.value( "status", "parsing_proof_not_found" )
        None
      }
    } catch {
      case e: Throwable =>
        metrics.value( "status", e match {
          case _: OutOfMemoryError   => "parsing_out_of_memory"
          case _: StackOverflowError => "parsing_stack_overflow"
          case _: Throwable          => "parsing_other_exception"
        } )
        metrics.value( "exception", e.toString )
        throw e
    }

    parseResult foreach {
      case ( expansionProof, backgroundTheory ) =>
        metrics.value( "has_equality", backgroundTheory.hasEquality )
        try metrics.time( "cutintro" ) {
          CutIntroduction.compressToLK( expansionProof, backgroundTheory, method = parseMethod( methodName ), verbose = false ) match {
            case Some( _ ) => metrics.value( "status", "ok" )
            case None =>
              if ( metricsPrinter.data( "termset_trivial" ) == true )
                metrics.value( "status", "cutintro_termset_trivial" )
              else
                metrics.value( "status", "cutintro_uncompressible" )
          }
        }
        catch {
          case e: Throwable =>
            metrics.value( "status", e match {
              case _: OutOfMemoryError                    => "cutintro_out_of_memory"
              case _: StackOverflowError                  => "cutintro_stack_overflow"
              case _: CutIntroUnprovableException         => "cutintro_ehs_unprovable"
              case _: CutIntroNonCoveringGrammarException => "cutintro_noncovering_grammar"
              case _: LKRuleCreationException             => "lk_rule_creation_exception"
              case _: Throwable                           => "cutintro_other_exception"
            } )
            metrics.value( "exception", e.toString )
            throw e
        }
    }
  }
}

object collectExperimentResults extends App {
  val metricsLineRegex = """METRICS (.*)""".r

  def parseOut( fn: File ) =
    JObject( fn.lines.collect {
      case metricsLineRegex( json ) => parse( json )
    }.collect {
      case JObject( map ) => map
    }.flatten.toList )

  val allResults = JArray( file".".glob( "**/stdout" ) map parseOut toList )
  print( compact( render( allResults ) ) )
}

object findNonTrivialTSTPExamples extends App {
  case class TermSetStats( file: File, size: Int, numFuns: Int )

  val p9Files = file"testing/TSTP/prover9".glob( "**/*.s" ).toSeq

  val stats = p9Files map { fn =>
    try {
      println( fn )
      withTimeout( 60 seconds ) {
        val p = Prover9Importer.expansionProof( fn )
        val terms = FOLInstanceTermEncoding( p.shallow ).encode( p )
        val functions = terms map { case FOLFunction( f, _ ) => f }

        Success( TermSetStats( fn, terms.size, functions.size ) )
      }
    } catch { case t: Throwable => Failure( t ) }
  }

  val interesting = stats flatMap { _.toOption } filter { s => s.size > s.numFuns }
  val trivial = stats flatMap { _.toOption } filter { s => s.size <= s.numFuns }

  val csv = new PrintWriter( "testing/resultsCutIntro/tstp_non_trivial_termset.csv" )
  interesting.sortBy( _.file.pathAsString ) foreach { s =>
    csv.println( s"${file".".relativize( s.file )},${s.numFuns},${s.size}" )
  }
  csv.close()

  var instance_per_formula = interesting map { s => s.size.toFloat / s.numFuns } sum
  var ts_size = interesting map { _.size } sum
  val avg_inst_per_form = instance_per_formula / interesting.size
  val avg_ts_size = ts_size.toFloat / interesting.size.toFloat

  val summary = new PrintWriter( "testing/resultsCutIntro/tstp_non_trivial_summary.txt" )
  summary.println( "Total number of proofs: " + stats.size )
  summary.println( "Total number of proofs with trivial termsets: " + trivial.size )
  summary.println( "Total number of proofs with non-trivial termsets: " + interesting.size )
  summary.println( "Time limit exceeded or exception: " + stats.collect { case Failure( t ) => t }.size )
  summary.println( "Average instances per quantified formula: " + avg_inst_per_form )
  summary.println( "Average termset size: " + avg_ts_size )
  summary.close()
}
