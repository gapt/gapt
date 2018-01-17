package at.logic.gapt.testing

import ammonite.ops.FilePath
import at.logic.gapt.expr.hol.CNFn
import at.logic.gapt.expr.{ Atom, Const }
import at.logic.gapt.proofs.expansion.{ eliminateCutsET, eliminateDefsET }
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.LogHandler

object testResolutionToExpansion extends scala.App {
  import at.logic.gapt.utils.logger._

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter

  try time( "total" ) {

    val Seq( p9proofFile, method ) = args.toSeq
    metric( "file", p9proofFile )
    metric( "method", method )

    val ( resolution0, endSequent ) = time( "p9import" ) {
      Prover9Importer.robinsonProofWithReconstructedEndSequent( FilePath( p9proofFile ), runFixDerivation = false )
    }
    metric( "size_res_dag", resolution0.dagLike.size )
    metric( "size_res_tree", resolution0.treeLike.size )

    val equational = containsEquationalReasoning( resolution0 )
    metric( "equational", equational )

    val proof = time( "extraction" ) {
      method match {
        case "vialk" =>
          val resolution = time( "fixderivation" ) { fixDerivation( resolution0, CNFn( endSequent.toImplication ) ) }
          val projections = time( "projections" ) {
            Map() ++ resolution.subProofs.collect {
              case in @ Input( clause ) =>
                in -> PCNF( endSequent, clause.map( _.asInstanceOf[Atom] ) )
            }
          }
          metric( "no_projs", projections.size )
          metric( "size_projs", projections.view.map( _._2.treeLike.size ).sum )
          val lk = time( "restolk" ) { ResolutionToLKProof( resolution, projections ) }
          metric( "size_lk_tree", lk.treeLike.size )
          metric( "size_lk_dag", lk.dagLike.size )
          time( "lktoexp" ) { LKToExpansionProof( lk ) }
        case "restoexp" =>
          val resolution = time( "fixderivation" ) { fixDerivation( resolution0, endSequent ) }
          metric( "size_res2_dag", resolution.dagLike.size )
          metric( "size_res2_tree", resolution.treeLike.size )
          implicit val ctx: Context = MutableContext.guess( resolution )
          val expansionWithDefs = time( "withdefs" ) {
            ResolutionToExpansionProof.withDefs(
              resolution,
              ResolutionToExpansionProof.inputsAsExpansionSequent )
          }
          metric( "size_withdefs", expansionWithDefs.size )
          // none of the stuff below should actually happen with prover9 proofs
          val defConsts = resolution.subProofs collect { case d: DefIntro => d.defConst: Const }
          val withDefsCE = time( "cutelim1" ) { eliminateCutsET( expansionWithDefs ) }
          val withoutDefs = time( "defelim" ) { eliminateDefsET( withDefsCE, !equational, defConsts ) }
          time( "cutelim2" ) { eliminateCutsET( withoutDefs ) }
      }
    }
    metric( "size_exp", proof.size )
    metric( "status", "ok" )

  } catch {
    case t: Throwable =>
      metric( "status", "exception" )
      metric( "exception", t.getMessage )
  }

}
