package at.logic.gapt.testing

import at.logic.gapt.expr.{ FOLFunction, EqC, constants }
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import java.io._
import java.nio.file.{ Paths, Files }
import at.logic.gapt.examples._
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.resolution.{ simplifyResolutionProof, numberOfResolutionsAndParamodulations, RobinsonToExpansionProof }
import at.logic.gapt.provers.maxsat.OpenWBO
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.glob
import at.logic.gapt.utils.logging.{ metrics, CollectMetrics }

import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.proofs.expansionTrees.{ FOLInstanceTermEncoding, addSymmetry, toShallow }

import org.json4s._
import org.json4s.native.JsonMethods._

import scala.collection.parallel.ForkJoinTaskSupport
import scala.concurrent.duration._
import scala.concurrent.forkjoin.ForkJoinPool
import scala.util.{ Success, Failure, Random }

object testCutIntro extends App {

  lazy val proofSeqRegex = """(\w+)\((\d+)\)""".r
  def loadProof( fileName: String ) = fileName match {
    case proofSeqRegex( name, n ) =>
      val p = proofSequences.find( _.name == name ).get( n.toInt )
      val hasEquality = containsEqualityReasoning( p )
      metrics.value( "lkinf_input", rulesNumber( p ) )
      Some( LKToExpansionProof( p ) -> hasEquality )
    case _ if fileName endsWith ".proof_flat" =>
      VeriTParser.getExpansionProof( fileName ) map { ep => addSymmetry( ep ) -> false }
    case _ if fileName contains "/leanCoP/" =>
      LeanCoPParser.getExpansionProof( fileName ) map { _ -> true }
    case _ if fileName contains "/prover9/" =>
      val ( resProof, endSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequentFromFile( fileName )
      metrics.value( "resinf_input", numberOfResolutionsAndParamodulations( simplifyResolutionProof( resProof ) ) )
      val expansionProof = RobinsonToExpansionProof( resProof, endSequent )
      val containsEquations = constants( toShallow( expansionProof ) ) exists {
        case EqC( _ ) => true
        case _        => false
      }
      Some( expansionProof -> containsEquations )
  }

  def getMethod( methodName: String ) = methodName match {
    case "1_dtable"    => DeltaTableMethod( manyQuantifiers = false )
    case "many_dtable" => DeltaTableMethod( manyQuantifiers = true )
    case "reforest"    => ReforestMethod()
    case _ if methodName endsWith "_maxsat" =>
      val vectorSizes = methodName.dropRight( "_maxsat".length ).split( "_" ).map( _.toInt )
      MaxSATMethod( OpenWBO, vectorSizes: _* )
  }

  lazy val proofs =
    ( for ( n <- 0 to 100; proofSequence <- proofSequences ) yield s"${proofSequence.name}($n)" ) ++
      glob( "testing/TSTP/prover9/**/*.s.out" ) ++
      glob( "testing/veriT-SMT-LIB/QF_UF/**/*.proof_flat" ) ++
      glob( "testing/TSTP/leanCoP/**/*.s.out" ) ++
      Nil

  lazy val methods = Seq( "1_dtable", "many_dtable", "1_maxsat", "1_1_maxsat", "2_maxsat", "2_2_maxsat", "reforest" )

  lazy val experiments = for ( p <- proofs; m <- methods ) yield ( p, m )

  def timeout = 60 seconds

  def runExperiment( fileName: String, methodName: String ): JValue = {
    val collectedMetrics = new CollectMetrics
    withTimeout( timeout ) {
      metrics.current.withValue( collectedMetrics ) {
        metrics.value( "file", fileName )
        metrics.value( "method", methodName )
        val parseResult = try metrics.time( "parse" ) {
          loadProof( fileName ) orElse {
            metrics.value( "status", "parsing_proof_not_found" )
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
          case e: Throwable =>
            metrics.value( "status", "parsing_other_exception" )
            None
        }

        parseResult foreach {
          case ( expansionProof, hasEquality ) =>
            metrics.value( "has_equality", hasEquality )
            try metrics.time( "cutintro" ) {
              CutIntroduction.compressToLK( expansionProof, hasEquality, getMethod( methodName ), verbose = false ) match {
                case Some( _ ) => metrics.value( "status", "ok" )
                case None =>
                  if ( collectedMetrics.data( "termset_trivial" ) == true )
                    metrics.value( "status", "cutintro_termset_trivial" )
                  else
                    metrics.value( "status", "cutintro_uncompressible" )
              }
            }
            catch {
              case e: ThreadDeath =>
                metrics.value( "status", "cutintro_timeout" )
              case e: OutOfMemoryError =>
                metrics.value( "status", "cutintro_out_of_memory" )
              case e: StackOverflowError =>
                metrics.value( "status", "cutintro_stack_overflow" )
              case e: CutIntroEHSUnprovableException =>
                metrics.value( "status", "cutintro_ehs_unprovable" )
              case e: CutIntroNonCoveringGrammarException =>
                metrics.value( "status", "cutintro_noncovering_grammar" )
              case e: LKRuleCreationException =>
                metrics.value( "status", "lk_rule_creation_exception" )
              case e: Throwable =>
                metrics.value( "status", "cutintro_other_exception" )
            }
        }
      }
    }

    val results = collectedMetrics.copy
    results.data.getOrElseUpdate( "status", "cutintro_timeout" )
    results.value( "phase", results.currentPhase )

    def jsonify( v: Any ): JValue = v match {
      case l: Long    => JInt( l )
      case l: Int     => JInt( l )
      case b: Boolean => JBool( b )
      case l: Seq[_]  => JArray( l map jsonify toList )
      case s          => JString( s toString )
    }

    JObject( results.data mapValues jsonify toList )
  }

  println( s"Running ${experiments.size} experiments." )

  val partialResultsOut = new PrintWriter( "partial_results.json" )
  var done = 0

  val parExperiments = Random.shuffle( experiments ).par
  parExperiments.tasksupport = new ForkJoinTaskSupport( new ForkJoinPool( Runtime.getRuntime.availableProcessors / 2 ) )
  val experimentResults = parExperiments flatMap {
    case ( p, m ) =>
      try {
        done += 1
        println( s"$done/${experiments.size}\t$p\t$m" )
        val beginTime = System.currentTimeMillis()
        val JObject( resultEntries ) =
          parse( runOutOfProcess[String]( Seq( "-Xmx2G", "-Xss30m" ) ) { compact( render( runExperiment( p, m ) ) ) } )
        val totalTime = System.currentTimeMillis() - beginTime
        val result = JObject( resultEntries :+ ( "time_total" -> JInt( totalTime ) ) )
        partialResultsOut.println( compact( render( result ) ) )
        partialResultsOut.flush()
        Some( result )
      } catch {
        case t: Throwable =>
          println( s"$p $m failed" )
          t.printStackTrace()
          None
      }
  }

  Files.write(
    Paths.get( "results.json" ),
    compact( render( JArray( experimentResults.toList ) ) ).getBytes
  )

  partialResultsOut.close()
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
