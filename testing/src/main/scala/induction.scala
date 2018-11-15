package gapt.testing

import ammonite.ops.FilePath
import gapt.expr.{ All, Eq, Var }
import gapt.formats.tip.TipSmtImporter
import gapt.proofs.gaptic.tactics.AnalyticInductionTactic
import gapt.proofs.gaptic.{ ProofState, Tactic }
import gapt.proofs.Ant
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.escargot.Escargot
import gapt.provers.maxsat.OpenWBO
import gapt.provers.smtlib.CVC4
import gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms, UntrustedFunctionalInductionAxioms }
import gapt.provers.viper.grammars.TreeGrammarProverOptions.Passthru
import gapt.provers.viper.grammars.{ TreeGrammarInductionTactic, TreeGrammarProverOptions }
import gapt.utils.{ LogHandler, Logger, MetricsPrinter }

object testInduction extends App {
  val logger = Logger( "testInduction" )

  class StrategyNotApplicable extends Exception

  def pickQuant( i: Int )( implicit ctx: Context ): Tactic[Unit] = {
    import gapt.proofs.gaptic._
    currentGoal.flatMap { goal =>
      val Some( All.Block( vs, _ ) ) = goal.conclusion.succedent.headOption
      if ( i < vs.size && ctx.getConstructors( vs( i ).ty ).isDefined ) introUnivsExcept( i )
      else throw new StrategyNotApplicable
    }
  }

  def resolveStrategy( strategyName: String )( implicit ctx: MutableContext ): Tactic[_] =
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
      case s if s.startsWith( "treeg_eq_" ) =>
        val ( Vector( quant ), eqs ) = s.substring( "treeg_eq_".size ).split( "_" ).map( _.toInt ).toVector.splitAt( 1 )
        import gapt.proofs.gaptic._
        for {
          goal <- currentGoal
          eqTheory = eqs.map( i => goal.conclusion( Ant( i ) ) ).collect { case All.Block( _, eq @ Eq( _, _ ) ) => eq }
          _ <- pickQuant( quant )
          _ <- treeGrammarInduction.
            maxsatSolver( OpenWBO ).
            equationalTheory( eqTheory: _* ).
            smtSolver( new CVC4( "UF", Seq( "--tlimit=300" ), treatUnknownAsSat = true ) ).
            smtEquationMode( Passthru )
        } yield ()
    }

  val Array( fileName: String, strategyName: String ) = args

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter
  def phase: String = metricsPrinter.data.getOrElse( "phase", "" ).toString

  logger.metric( "filename", fileName )
  logger.metric( "strategy", strategyName )
  try logger.time( "total" ) {
    val tipProblem = logger.time( "tip" ) { TipSmtImporter.fixupAndLoad( FilePath( fileName ) ) }
    implicit val ctx: MutableContext = tipProblem.ctx.newMutable
    logger.metric( "goal", tipProblem.goal.toSigRelativeString )
    val proof = logger.time( "prover" ) {
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

object computeStrategies extends scala.App {
  def printStrategy( fileName: String, strategy: String ): Unit =
    println( s"$fileName $strategy" )

  args foreach { fileName =>
    try {
      val problem = TipSmtImporter.fixupAndLoad( FilePath( fileName ) )
      import problem.ctx
      val sequent = problem.toSequent
      val All.Block( goalQuants, _ ) = sequent.succedent.head
      val inductiveGoalQuantIdcs =
        for {
          ( q @ Var( _, t ), i ) <- goalQuants.zipWithIndex
          if ctx.getConstructors( t ).isDefined
        } yield i
      val equationIdcs = for ( ( All.Block( _, Eq( _, _ ) ), i ) <- sequent.antecedent.zipWithIndex ) yield i
      val equationIdxSubsets = ( 0 to 2 ).flatMap( equationIdcs.toSet.subsets )
      for ( goalQuant <- inductiveGoalQuantIdcs; eqTh <- equationIdxSubsets )
        printStrategy(
          fileName,
          if ( eqTh.isEmpty ) s"treeg_default$goalQuant" else
            "treeg_eq_" + ( goalQuant +: eqTh.toVector ).mkString( "_" ) )
    } catch {
      case t: Throwable => Console.err.println( s"$fileName: ${t.getMessage}" )
    }
  }
}