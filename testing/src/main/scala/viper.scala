package gapt.testing

import java.io.PrintWriter

import gapt.utils._
import org.json4s._
import org.json4s.native.JsonMethods._

import scala.concurrent.duration._
import ammonite.ops._
import gapt.expr.formula.{ All, Formula, Imp }
import gapt.formats.tip.TipSmtImporter
import gapt.proofs.expansion.ExpansionProofToLK
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.transformations.{ LKToExpansionProof, cleanStructuralRules, inductionNormalForm }
import gapt.proofs.lk.util.extractInductionAxioms
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
  def countInductions( prf: LKProof, axioms: Set[Formula] ): ( Int, Int ) = {
    def go( prf: LKProof ): ( Int, Int ) = {
      if ( prf.name == "cut" ) {
        prf.immediateSubProofs.head.conclusion.succedent match {
          case Seq( p ) if axioms.contains( p ) =>
            val ( n, d ) = prf.immediateSubProofs.tail.map( go ).foldLeft( ( 0, 0 ) ) {
              case ( ( l1, r1 ), ( l2, r2 ) ) => ( l1 + l2, r1 max r2 )
            }

            ( n + 1, d + 1 )
          case _ =>
            prf.immediateSubProofs.map( go ).foldLeft( ( 0, 0 ) ) {
              case ( ( l1, r1 ), ( l2, r2 ) ) => ( l1 + l2, r1 max r2 )
            }
        }
      } else {
        prf.immediateSubProofs.map( go ).foldLeft( ( 0, 0 ) ) {
          case ( ( l1, r1 ), ( l2, r2 ) ) => ( l1 + l2, r1 max r2 )
        }
      }
    }

    go( prf )
  }

  def cleanProof( prf: LKProof ): LKProof = {
    val prf1 = cleanStructuralRules( prf )
    val expPrf = LKToExpansionProof( prf1 )
    ExpansionProofToLK( expPrf ).toOption.get
  }

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
      TipSmtImporter.fixupAndLoad( fileName )
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
      withTimeout( 60 seconds ) {
        Viper( problem, options ) match {
          case Some( prf1 ) =>
            logger.metric( "status", "ok" )
            val axioms = extractInductionAxioms( prf1 )( problem.ctx ).toSet
            val ( inds1, depth1 ) = countInductions( prf1, axioms )
            val prf2 = cleanProof( prf1 )
            val ( inds2, depth2 ) = countInductions( prf2, axioms )

            logger.metric( "inductions_init", inds1 )
            logger.metric( "max_ind_depth_init", depth1 )
            logger.metric( "inductions_clean", inds2 )
            logger.metric( "max_ind_depth_clean", depth2 )
          case None => logger.metric( "status", "saturated" )
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
