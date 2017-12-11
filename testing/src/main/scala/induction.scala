package at.logic.gapt.testing

import ammonite.ops.FilePath
import at.logic.gapt.expr.All
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic
import at.logic.gapt.proofs.gaptic.{ ProofState, Tactical }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.maxsat.OpenWBO
import at.logic.gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms, UntrustedFunctionalInductionAxioms }
import at.logic.gapt.provers.viper.grammars.{ TreeGrammarInductionTactic, TreeGrammarProverOptions }
import at.logic.gapt.utils.{ LogHandler, logger }

object testInduction extends App {

  class StrategyNotApplicable extends Exception

  def pickQuant( i: Int )( implicit ctx: Context ): Tactical[Unit] = {
    import at.logic.gapt.proofs.gaptic._
    currentGoal.flatMap { goal =>
      val Some( All.Block( vs, _ ) ) = goal.conclusion.succedent.headOption
      if ( i < vs.size && ctx.getConstructors( vs( i ).ty ).isDefined ) introUnivsExcept( i )
      else throw new StrategyNotApplicable
    }
  }

  def resolveStrategy( strategyName: String )( implicit ctx: MutableContext ): Tactical[_] =
    strategyName match {
      case "ana_indep"  => AnalyticInductionTactic( IndependentInductionAxioms(), Escargot )
      case "ana_seq"    => AnalyticInductionTactic( SequentialInductionAxioms(), Escargot )
      case "ana_funind" => AnalyticInductionTactic( UntrustedFunctionalInductionAxioms, Escargot )
      case s if s.startsWith( "treeg_noquant" ) =>
        pickQuant( strategyName.substring( "treeg_noquant".size ).toInt ).andThen(
          new TreeGrammarInductionTactic( TreeGrammarProverOptions( quantTys = Some( Seq() ), maxSATSolver = OpenWBO ) ) )
      case s if s.startsWith( "treeg_default" ) =>
        pickQuant( strategyName.substring( "treeg_default".size ).toInt ).andThen(
          new TreeGrammarInductionTactic( TreeGrammarProverOptions( maxSATSolver = OpenWBO ) ) )
    }

  val Array( fileName: String, strategyName: String ) = args

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter
  def phase: String = metricsPrinter.data.getOrElse( "phase", "" ).toString

  logger.metric( "filename", fileName )
  logger.metric( "strategy", strategyName )
  try logger.time( "prover" ) {
    val tipProblem = logger.time( "tip" ) { TipSmtParser.fixupAndParse( FilePath( fileName ) ) }
    implicit val ctx: MutableContext = tipProblem.ctx.newMutable
    logger.metric( "goal", tipProblem.goal.toSigRelativeString )
    val proof = logger.time( "strategy" ) {
      ( ProofState( tipProblem.toSequent ) + resolveStrategy( strategyName ) ).result
    }
    logger.time( "check" ) { ctx.check( proof ) }
    logger.metric( "status", "ok" )
  } catch {
    case t: StrategyNotApplicable =>
      logger.metric( "status", "na" )
    case t: Throwable =>
      logger.metric( "exception", t.toString )
      logger.metric( "status", s"exception" )
  }
}