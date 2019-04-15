package gapt.testing

import java.io.PrintWriter

import gapt.utils._
import org.json4s._
import org.json4s.native.JsonMethods._

import scala.concurrent.duration._
import ammonite.ops._
import gapt.formats.tip.TipSmtImporter
import gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms }
import gapt.provers.viper.{ AipOptions, Viper, ViperOptions }

object parseMode {
  def apply( modeName: String ): ViperOptions = modeName match {
    case "analytic_sequential"  => ViperOptions( mode = "analytic", aipOptions = AipOptions( axioms = SequentialInductionAxioms() ) )
    case "analytic_independent" => ViperOptions( mode = "analytic", aipOptions = AipOptions( axioms = IndependentInductionAxioms() ) )
    case "treegrammar"          => ViperOptions( mode = "treegrammar" )
    case "spind"                => ViperOptions( mode = "spind" )
  }
}

object testViper extends App {
  val logger = Logger( "testViper" )

  val ( fileName, mode ) =
    args.toList match {
      case Seq( f, m ) => ( f, m )
    }

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter
  logger.metric( "file", fileName )
  logger.metric( "mode", mode )

  logger.time( "total" ) {
    val problem = try logger.time( "parse" ) {
      TipSmtImporter.load( fileName )
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

    val options = parseMode( mode )

    try logger.time( "viper" ) {
      withTimeout( 45 seconds ) {
        Viper( problem, options ) match {
          case Some( _ ) => logger.metric( "status", "ok" )
          case None      => logger.metric( "status", "saturated" )
        }
      }
    }
    catch {
      case e: Throwable =>
        logger.metric( "status", e match {
          case _: OutOfMemoryError   => "viper_out_of_memory"
          case _: StackOverflowError => "viper_stack_overflow"
          case _: TimeOutException   => "viper_timeout"
          case _: Throwable          => "viper_other_exception"
        } )
        logger.metric( "exception", e.toString )
        throw e
    }
  }
}
