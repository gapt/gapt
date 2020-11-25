package gapt.testing

import gapt.expr.Expr
import gapt.expr.formula.hol.{ containsQuantifier, isExtendedAtom }
import gapt.expr.formula.{ All, Formula, Imp }
import gapt.utils._

import scala.concurrent.duration._
import gapt.formats.tip.TipSmtImporter
import gapt.proofs.context.Context
import gapt.proofs.expansion.ExpansionProofToLK
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.transformations.{ LKToExpansionProof, cleanStructuralRules }
import gapt.proofs.lk.util.extractInductionAxioms
import gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms }
import gapt.provers.viper.spin.SpinOptions
import gapt.provers.viper.{ AipOptions, Viper, ViperOptions }

object parseMode {
  def apply( modeName: String ): ViperOptions = modeName match {
    case "analytic_sequential"  => ViperOptions( mode = "analytic", aipOptions = AipOptions( axioms = SequentialInductionAxioms() ) )
    case "analytic_independent" => ViperOptions( mode = "analytic", aipOptions = AipOptions( axioms = IndependentInductionAxioms() ) )
    case "treegrammar"          => ViperOptions( mode = "treegrammar" )
    case "spin"                 => ViperOptions( mode = "spin" )
    case "spin_nogen"           => ViperOptions( mode = "spin", spinOptions = SpinOptions( performGeneralization = false ) )
    case "spin_notest"          => ViperOptions( mode = "spin", spinOptions = SpinOptions( sampleTestTerms = 0 ) )
  }
}

object testViper extends App {
  def countInductions( prf: LKProof ): ( Int, Int ) = {
    val ( n, d ) = prf.immediateSubProofs.map( countInductions ).foldLeft( ( 0, 0 ) ) {
      case ( ( n1, d1 ), ( n2, d2 ) ) => ( n1 + n2, d1 max d2 )
    }

    prf match {
      case InductionRule( _, _, _ ) => ( n + 1, d + 1 )
      case _                        => ( n, d )
    }
  }

  // This turns the cuts into induction inferences
  def cleanProof( prf: LKProof )( implicit ctx: Context ): LKProof = {
    val prf1 = cleanStructuralRules( prf )
    val expPrf = LKToExpansionProof( prf1 )( ctx )
    ExpansionProofToLK( expPrf )( ctx ).toOption.get
  }

  def removeOuterAlls( e: Expr ): Expr =
    e match {
      case All( _, e1 ) => removeOuterAlls( e1 )
      case _            => e
    }

  def inductionTarget( e: Expr ): Expr =
    removeOuterAlls( e ) match {
      case Imp( _, e1 ) => removeOuterAlls( e1 )
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

    var prf: Option[LKProof] = None

    try logger.time( "viper" ) {
      withTimeout( 120 seconds ) {
        Viper( problem, options ) match {
          case Some( prf1 ) =>
            logger.metric( "status", "ok" )
            prf = Some( prf1 )
          case None => logger.metric( "status", "saturated" )
        }
      }
    } catch {
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

    prf match {
      case None =>
      case Some( prf1 ) =>
        val prf2 = cleanProof( prf1 )( problem.ctx )
        val ( inds, depth ) = countInductions( prf2 )

        logger.metric( "inductions", inds )
        logger.metric( "induction_depth", depth )

        val axs = extractInductionAxioms( prf2 )( problem.ctx )
        val targets = axs.map( inductionTarget )

        val atomic = targets.count( e => isExtendedAtom( e.asInstanceOf[Formula] ) )
        val quantified = targets.count( e => containsQuantifier( e.asInstanceOf[Formula] ) )

        logger.metric( "atomic", atomic )
        logger.metric( "quantified", quantified )
    }

  }
}
