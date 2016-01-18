package at.logic.gapt.testing

import at.logic.gapt.expr.{ FOLFunction, EqC, constants }
import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.sketch.RefutationSketchToRobinson
import at.logic.gapt.utils.logging.MetricsCollector
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import java.io._
import at.logic.gapt.examples._
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.lk._
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, simplifyResolutionProof, numberOfResolutionsAndParamodulations, RobinsonToExpansionProof }
import at.logic.gapt.provers.maxsat.OpenWBO
import at.logic.gapt.provers.prover9.{ Prover9, Prover9Importer }
import at.logic.gapt.utils.glob
import at.logic.gapt.utils.logging.metrics

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.proofs.expansion._

import org.json4s._
import org.json4s.native.JsonMethods._

import scala.collection.mutable
import scala.concurrent.duration._
import scala.io.Source
import scala.util.{ Success, Failure }

class MetricsPrinter extends MetricsCollector {
  val data = mutable.Map[String, Any]()

  def jsonify( v: Any ): JValue = v match {
    case l: Long    => JInt( l )
    case l: Int     => JInt( l )
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

object testCutIntro extends App {

  lazy val proofSeqRegex = """(\w+)\((\d+)\)""".r
  def loadProof( fileName: String ): Option[( ExpansionProof, Boolean )] = fileName match {
    case proofSeqRegex( name, n ) =>
      val p = proofSequences.find( _.name == name ).get( n.toInt )
      val hasEquality = containsEqualityReasoning( p )
      metrics.value( "lkinf_input", rulesNumber( p ) )
      Some( eliminateCutsET( LKToExpansionProof( p ) ) -> hasEquality )
    case _ if fileName endsWith ".proof_flat" =>
      VeriTParser.getExpansionProof( fileName ) map { ep => ExpansionProof( addSymmetry( ep ) ) -> false }
    case _ if fileName contains "/leanCoP" =>
      LeanCoPParser.getExpansionProof(
        new StringReader( extractFromTSTPCommentsIfNecessary( Source.fromFile( fileName ).mkString ) )
      ) map { ExpansionProof( _ ) -> true }
    case _ if fileName contains "/Prover9" =>
      val ( resProof, endSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequent(
        extractFromTSTPCommentsIfNecessary( Source.fromFile( fileName ).mkString )
      )
      Some( loadResolutionProof( resProof, endSequent ) )
    case _ => // try tstp format
      val tstpOutput = Source fromFile fileName mkString

      metrics.value( "tstp_is_cnf_ref", tstpOutput contains "CNFRefutation" )

      val ( endSequent, sketch ) = TptpProofParser parse tstpOutput
      metrics.value( "tstp_sketch_size", sketch.subProofs.size )

      RefutationSketchToRobinson( sketch ) map { resProof =>
        loadResolutionProof( resProof, endSequent )
      } toOption
  }

  def extractFromTSTPCommentsIfNecessary( output: String ): String = {
    val lines = output.split( "\n" )
    if ( lines contains "%----ERROR: Could not form TPTP format derivation" )
      lines.toSeq.
        dropWhile( _ != "%----ORIGINAL SYSTEM OUTPUT" ).drop( 1 ).
        takeWhile( !_.startsWith( "%-----" ) ).dropRight( 1 ).
        map { _ substring 2 }.
        dropWhile( _ startsWith "% " ).drop( 1 ).
        filterNot( _ startsWith "% SZS" ).
        filterNot( _ startsWith "\\n% SZS" ).
        mkString( "", "\n", "\n" )
    else
      output
  }

  def loadResolutionProof( resProof: ResolutionProof, endSequent: HOLSequent ) = {
    metrics.value( "resinf_input", numberOfResolutionsAndParamodulations( simplifyResolutionProof( resProof ) ) )
    val expansionProof = RobinsonToExpansionProof( resProof, endSequent )
    val containsEquations = constants( toShallow( expansionProof ) ) exists {
      case EqC( _ ) => true
      case _        => false
    }
    expansionProof -> containsEquations
  }

  def getMethod( methodName: String ) = methodName match {
    case "1_dtable"    => DeltaTableMethod( manyQuantifiers = false )
    case "many_dtable" => DeltaTableMethod( manyQuantifiers = true )
    case "reforest"    => ReforestMethod()
    case _ if methodName endsWith "_maxsat" =>
      val vectorSizes = methodName.dropRight( "_maxsat".length ).split( "_" ).map( _.toInt )
      MaxSATMethod( OpenWBO, vectorSizes: _* )
  }

  val Array( fileName: String, methodName: String ) = args

  val metricsPrinter = new MetricsPrinter
  metrics.current.value = metricsPrinter
  metrics.value( "file", fileName )
  metrics.value( "method", methodName )

  metrics.time( "total" ) {
    val parseResult = try metrics.time( "parse" ) {
      loadProof( fileName ) orElse {
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
        throw e
    }

    parseResult foreach {
      case ( expansionProof, hasEquality ) =>
        metrics.value( "has_equality", hasEquality )
        try metrics.time( "cutintro" ) {
          CutIntroduction.compressToLK( expansionProof, hasEquality, getMethod( methodName ), verbose = false ) match {
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
              case _: CutIntroEHSUnprovableException      => "cutintro_ehs_unprovable"
              case _: CutIntroNonCoveringGrammarException => "cutintro_noncovering_grammar"
              case _: LKRuleCreationException             => "lk_rule_creation_exception"
              case _: Throwable                           => "cutintro_other_exception"
            } )
            throw e
        }
    }
  }
}

object collectExperimentResults extends App {
  val metricsLineRegex = """METRICS (.*)""".r

  def parseOut( fn: String ) =
    JObject( Source.fromFile( fn ).getLines().collect {
      case metricsLineRegex( json ) => parse( json )
    }.collect {
      case JObject( map ) => map
    }.flatten.toList )

  val allResults = JArray( glob( "**/stdout" ) map parseOut toList )
  print( compact( render( allResults ) ) )
}

object findNonTrivialTSTPExamples extends App {
  case class TermSetStats( fileName: String, size: Int, numFuns: Int )

  val p9Files = glob( "testing/TSTP/prover9/**/*.s.out" )

  val stats = p9Files map { fn =>
    try {
      println( fn )
      withTimeout( 60 seconds ) {
        val p = Prover9Importer.expansionProofFromFile( fn )
        val terms = FOLInstanceTermEncoding( toShallow( p ) ).encode( p )
        val functions = terms map { case FOLFunction( f, _ ) => f }

        Success( TermSetStats( fn, terms.size, functions.size ) )
      }
    } catch { case t: Throwable => Failure( t ) }
  }

  val interesting = stats flatMap { _.toOption } filter { s => s.size > s.numFuns }
  val trivial = stats flatMap { _.toOption } filter { s => s.size <= s.numFuns }

  val csv = new PrintWriter( "testing/resultsCutIntro/tstp_non_trivial_termset.csv" )
  interesting.sortBy( _.fileName ) foreach { s =>
    csv.println( s"${s.fileName},${s.numFuns},${s.size}" )
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
