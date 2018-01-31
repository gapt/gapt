package at.logic.gapt.testing

import ammonite.ops.FilePath
import at.logic.gapt.expr.hol.containsQuantifierOnLogicalLevel
import at.logic.gapt.proofs.expansion.ExpansionProofToLK
import at.logic.gapt.proofs.lk.{ LKToND, containsEqualityReasoning }
import at.logic.gapt.proofs.loadExpansionProof
import at.logic.gapt.proofs.nd.ExcludedMiddleRule
import at.logic.gapt.utils.{ LogHandler, Logger }

// TODO: run on TPTP problems (not proofs), and do deskolemization

object testLKToND extends scala.App {
  val logger = Logger( "testLKToND" )
  import logger._

  val metricsPrinter = new MetricsPrinter
  LogHandler.current.value = metricsPrinter

  try time( "total" ) {

    val Seq( fileName ) = args.toSeq
    metric( "file", fileName )

    val expansion = time( "import" ) { loadExpansionProof( FilePath( fileName ) ) }
    metric( "size_exp", expansion.size )

    val Right( lk ) = time( "exp2lk" ) { ExpansionProofToLK.withIntuitionisticHeuristics( expansion ) }
    metric( "size_lk", lk.treeLike.size )
    metric( "equational", containsEqualityReasoning( lk ) )
    metric( "lk_max_succ_size", lk.subProofs.map( _.endSequent.succedent.size ).max )
    metric( "lk_max_succ_set_size", lk.subProofs.map( _.endSequent.succedent.toSet.size ).max )

    val nd = time( "lk2nd" ) { LKToND( lk ) }
    metric( "size_nd", nd.treeLike.size )

    metric( "num_excl_mid", nd.treeLike.postOrder.count {
      case _: ExcludedMiddleRule => true
      case _                     => false
    } )
    metric( "num_quant_excl_mid", nd.treeLike.postOrder.count {
      case em: ExcludedMiddleRule if containsQuantifierOnLogicalLevel( em.formulaA ) => true
      case _ => false
    } )

    metric( "status", "ok" )

  } catch {
    case t: Throwable =>
      metric( "status", "exception" )
      metric( "exception", t.getMessage )
  }

}
