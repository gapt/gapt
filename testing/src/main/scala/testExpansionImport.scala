package gapt.testing
import os.FilePath
import gapt.expr.formula.hol.lcomp
import gapt.expr.Const
import gapt.expr.util.expressionSize
import gapt.formats.tptp.TptpImporter
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion.eliminateCutsET
import gapt.proofs.expansion.eliminateDefsET
import gapt.proofs.resolution._
import gapt.proofs.RichFormulaSequent
import gapt.provers.eprover.EProver
import gapt.utils.{LogHandler, Logger, MetricsPrinter}
import gapt.proofs.HOLSequent

object testExpansionImport extends scala.App {
  val logger = Logger("testExpansionImport")
  import logger._

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter

  val Seq(tptpFileName) = args.toSeq
  metric("file", tptpFileName)

  try time("total") {
      val tptp = time("tptpparser") { TptpImporter.loadWithIncludes(FilePath(tptpFileName)) }
      val problem: HOLSequent = tptp.toSequent
      metric("problem_lcomp", lcomp(problem))
      metric("problem_scomp", expressionSize(problem.toImplication))
      implicit val ctx = MutableContext.guess(problem)
      val cnf = time("clausifier") { structuralCNF(problem) }

      time("prover") { new EProver(Seq("--auto-schedule", "--soft-cpu-limit=60", "--memory-limit=2048")).getResolutionProof(cnf) } match {
        case Some(resolution) =>
          metric("size_res_dag", resolution.dagLike.size)
          metric("size_res_tree", resolution.treeLike.size)
          val equational = containsEquationalReasoning(resolution)
          metric("equational", equational)
          val expansionWithDefs = time("withdefs") {
            ResolutionToExpansionProof.withDefs(
              resolution,
              ResolutionToExpansionProof.inputsAsExpansionSequent
            )
          }
          metric("size_withdefs", expansionWithDefs.size)
          val defConsts = resolution.subProofs collect { case d: DefIntro => d.defConst: Const }
          val withDefsCE = time("cutelim1") { eliminateCutsET(expansionWithDefs) }
          val withoutDefs = time("defelim") { eliminateDefsET(withDefsCE, !equational, defConsts) }
          val expansion = time("cutelim2") { eliminateCutsET(withoutDefs) }
          metric("size_exp", expansion.size)
          metric("status", "unsat")
        case None =>
          metric("status", "sat")
      }
    }
  catch {
    case t: Throwable =>
      metric("status", "exception")
      metric("exception", t.getMessage.take(100))
  }

}
