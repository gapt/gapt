package gapt.testing

import java.io.PrintWriter

import gapt.cutintro._
import gapt.examples._
import gapt.expr.{ Apps, FOLVar }
import gapt.grammars.DeltaTableMethod
import gapt.proofs.expansion._
import gapt.proofs.lk._
import gapt.proofs.loadExpansionProof
import gapt.provers.maxsat.OpenWBO
import gapt.provers.prover9.Prover9Importer
import gapt.provers.smtlib.ExternalSmtlibProgram
import gapt.utils._
import org.json4s._
import org.json4s.native.JsonMethods._

import scala.collection.mutable
import scala.concurrent.duration._
import scala.util.{ Failure, Success }
import ammonite.ops._
import gapt.utils.LogHandler.VerbosityLevel

class MetricsPrinter extends LogHandler {
  val data: mutable.Map[String, Any] = mutable.Map[String, Any]()

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

  val phaseStack: mutable.Buffer[String] = mutable.Buffer()
  override def timeBegin( domain: String, level: VerbosityLevel, key: String, desc: String ): Unit = {
    phaseStack += key
    value( "phase", key )
    value( s"started_$phase", true )
    value( s"in_$phase", true )
  }
  override def time( domain: String, level: VerbosityLevel, key: String, desc: String, duration: Duration ): Unit = {
    value( s"time_$key", duration.toMillis )
    value( s"in_$phase", false )
    value( s"ended_$phase", true )
    phaseStack.trimEnd( 1 )
  }
  def phase: String = phaseStack.last

  override def metric( domain: String, level: VerbosityLevel, key: String, desc: String, v: => Any ): Unit =
    value( key, v )

  def value( key: String, value: => Any ) = {
    data( key ) = value
    println( s"METRICS ${compact( render( JObject( key -> jsonify( data( key ) ) ) ) )}" )
  }

  override def message( domain: String, level: VerbosityLevel, msg: => Any ): Unit = ()
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
  val logger = Logger( "testCutIntro" )

  val Array( fileName: String, methodName: String ) = args

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter
  logger.metric( "file", fileName )
  logger.metric( "method", methodName )

  val proofSeqRegex = """(\w+)\((\d+)\)""".r
  def loadProofForCutIntro( fileName: String ) = fileName match {
    case proofSeqRegex( name, n ) =>
      val p = proofSequences.find( _.name == name ).get( n.toInt )
      logger.metric( "lkinf_input", rulesNumber( p ) )
      CutIntroduction.InputProof.fromLK( p )
    case _ =>
      val ( exp, bgTh ) = loadExpansionProof.withBackgroundTheory( FilePath( fileName ) )
      CutIntroduction.InputProof( exp, bgTh )
  }

  logger.time( "total" ) {
    val inputProof = try logger.time( "parse" ) {
      loadProofForCutIntro( fileName )
    } catch {
      case e: Throwable =>
        logger.metric( "status", e match {
          case _: OutOfMemoryError   => "parsing_out_of_memory"
          case _: StackOverflowError => "parsing_stack_overflow"
          case _: Throwable          => "parsing_other_exception"
        } )
        logger.metric( "exception", e.toString )
        throw e
    }

    logger.metric( "has_equality", inputProof.backgroundTheory.hasEquality )
    try logger.time( "cutintro" ) {
      CutIntroduction( inputProof, method = parseMethod( methodName ) ) match {
        case Some( _ ) => logger.metric( "status", "ok" )
        case None =>
          if ( metricsPrinter.data( "termset_trivial" ) == true )
            logger.metric( "status", "cutintro_termset_trivial" )
          else
            logger.metric( "status", "cutintro_uncompressible" )
      }
    }
    catch {
      case e: Throwable =>
        logger.metric( "status", e match {
          case _: OutOfMemoryError => "cutintro_out_of_memory"
          case _: StackOverflowError => "cutintro_stack_overflow"
          case _: CutIntroduction.UnprovableException => "cutintro_ehs_unprovable"
          case _: CutIntroduction.NonCoveringGrammarException => "cutintro_noncovering_grammar"
          case _: LKRuleCreationException => "lk_rule_creation_exception"
          case _: ExternalSmtlibProgram.UnexpectedTerminationException => s"timeout_${metricsPrinter.data( "phase" )}"
          case _: Throwable => "cutintro_other_exception"
        } )
        logger.metric( "exception", e.toString )
        throw e
    }
  }
}

object testPi2CutIntro extends App {
  val logger = Logger( "testPi2CutIntro" )

  val Array( fileName: String, numBetas: String ) = args

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter
  logger.metric( "file", fileName )
  logger.metric( "num_betas", numBetas )

  val proofSeqRegex = """(\w+)\((\d+)\)""".r
  def loadProofForCutIntro( fileName: String ) = fileName match {
    case proofSeqRegex( name, n ) =>
      val p = proofSequences.find( _.name == name ).get( n.toInt )
      logger.metric( "lkinf_input", rulesNumber( p ) )
      CutIntroduction.InputProof.fromLK( p )
    case _ =>
      val ( exp, bgTh ) = loadExpansionProof.withBackgroundTheory( FilePath( fileName ) )
      CutIntroduction.InputProof( exp, bgTh )
  }

  logger.time( "total" ) {
    val inputProof = try logger.time( "parse" ) {
      loadProofForCutIntro( fileName )
    } catch {
      case e: Throwable =>
        logger.metric( "status", e match {
          case _: OutOfMemoryError   => "parsing_out_of_memory"
          case _: StackOverflowError => "parsing_stack_overflow"
          case _: Throwable          => "parsing_other_exception"
        } )
        logger.metric( "exception", e.toString )
        throw e
    }

    if ( inputProof.backgroundTheory.hasEquality ) {
      logger.metric( "status", "has_equality" )
    } else {
      try logger.time( "cutintro" ) {
        val alpha = FOLVar( "x" )
        val betas = for ( i <- 1 to numBetas.toInt ) yield FOLVar( s"y$i" )
        Pi2CutIntroduction( inputProof, alpha, betas.toVector, OpenWBO ) match {
          case Some( _ ) => logger.metric( "status", "ok" )
          case None =>
            if ( metricsPrinter.data( "lang_trivial" ) == true )
              logger.metric( "status", "cutintro_lang_trivial" )
            else
              logger.metric( "status", "cutintro_uncompressible" )
        }
      }
      catch {
        case e: Throwable =>
          logger.metric( "status", e match {
            case _: OutOfMemoryError => "cutintro_out_of_memory"
            case _: StackOverflowError => "cutintro_stack_overflow"
            case _: CutIntroduction.UnprovableException => "cutintro_ehs_unprovable"
            case _: CutIntroduction.NonCoveringGrammarException => "cutintro_noncovering_grammar"
            case _: LKRuleCreationException => "lk_rule_creation_exception"
            case _: ExternalSmtlibProgram.UnexpectedTerminationException => s"timeout_${metricsPrinter.data( "phase" )}"
            case _: Throwable => "cutintro_other_exception"
          } )
          logger.metric( "exception", e.toString )
          throw e
      }
    }
  }
}

object collectExperimentResults extends App {
  val metricsLineRegex = """METRICS (.*)""".r

  def parseOut( fn: Path ) =
    JObject(
      read.lines( fn ).collect {
        case metricsLineRegex( json ) => parse( json )
      }.collect {
        case JObject( map ) => map
      }.flatten
        .groupBy( _._1 ).map {
          case ( k, vs ) if k.startsWith( "time_" ) =>
            k -> JInt( vs.collect { case ( _, JInt( x ) ) => x }.sum )
          case ( k, vs ) => k -> vs.last._2
        }.toList )

  val allResults = JArray( ls.rec( pwd ).filter( _.last == "stdout" ).map( parseOut ).toList )
  print( compact( render( allResults ) ) )
}

object findNonTrivialTSTPExamples extends App {
  case class TermSetStats( file: Path, size: Int, numFuns: Int )

  val p9Files = ls.rec( pwd / "testing" / "TSTP" / "prover9" ).filter( _.ext == "s" )

  val stats = p9Files map { fn =>
    try {
      println( fn )
      withTimeout( 60 seconds ) {
        val p = Prover9Importer.expansionProof( fn )
        val terms = InstanceTermEncoding( p.shallow ).encode( p )
        val functions = terms map { case Apps( f, _ ) => f }

        Success( TermSetStats( fn, terms.size, functions.size ) )
      }
    } catch { case t: Throwable => Failure( t ) }
  }

  val interesting = stats flatMap { _.toOption } filter { s => s.size > s.numFuns }
  val trivial = stats flatMap { _.toOption } filter { s => s.size <= s.numFuns }

  val csv = new PrintWriter( "testing/resultsCutIntro/tstp_non_trivial_termset.csv" )
  interesting.sortBy( _.file.toString ) foreach { s =>
    csv.println( s"${s.file relativeTo pwd},${s.numFuns},${s.size}" )
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
