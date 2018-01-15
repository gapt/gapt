package at.logic.gapt.testing
import ammonite.ops.FilePath
import at.logic.gapt.expr.{ Const, expressionSize }
import at.logic.gapt.expr.hol.lcomp
import at.logic.gapt.formats.tptp.TptpParser
import at.logic.gapt.proofs.MutableContext
import at.logic.gapt.proofs.expansion.{ eliminateCutsET, eliminateDefsET }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.utils.LogHandler

object testExpansionImport extends scala.App {
  import at.logic.gapt.utils.logger._

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter

  val Seq( tptpFileName ) = args.toSeq
  metric( "file", tptpFileName )

  try time( "total" ) {
    val tptp = time( "tptpparser" ) { TptpParser.load( FilePath( tptpFileName ) ) }
    val problem = tptp.toSequent
    metric( "problem_lcomp", lcomp( problem ) )
    metric( "problem_scomp", expressionSize( problem.toImplication ) )
    implicit val ctx = MutableContext.guess( problem )
    val cnf = time( "clausifier" ) { structuralCNF( problem ) }

    time( "prover" ) { new EProver( Seq( "--auto-schedule", "--soft-cpu-limit=60", "--memory-limit=2048" ) ).getResolutionProof( cnf ) } match {
      case Some( resolution ) =>
        metric( "size_res_dag", resolution.dagLike.size )
        metric( "size_res_tree", resolution.treeLike.size )
        val equational = containsEquationalReasoning( resolution )
        metric( "equational", equational )
        val expansionWithDefs = time( "withdefs" ) {
          ResolutionToExpansionProof.withDefs(
            resolution,
            ResolutionToExpansionProof.inputsAsExpansionSequent )
        }
        metric( "size_withdefs", expansionWithDefs.size )
        val defConsts = resolution.subProofs collect { case d: DefIntro => d.defConst: Const }
        val withDefsCE = time( "cutelim1" ) { eliminateCutsET( expansionWithDefs ) }
        val withoutDefs = time( "defelim" ) { eliminateDefsET( withDefsCE, !equational, defConsts ) }
        val expansion = time( "cutelim2" ) { eliminateCutsET( withoutDefs ) }
        metric( "size_exp", expansion.size )
        metric( "status", "unsat" )
      case None =>
        metric( "status", "sat" )
    }
  } catch {
    case t: Throwable =>
      metric( "status", "exception" )
      metric( "exception", t.getMessage )
  }

}
