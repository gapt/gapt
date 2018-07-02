package gapt.formats.verit

import gapt.expr.{ TBase, Const }
import gapt.proofs.HOLSequent
import gapt.provers.Session._
import gapt.provers.Session.Runners._

object SmtLibExporter {

  /**
   *  Takes a sequent and generates the SMT-LIB benchmark as a string.
   *
   * @param s Sequent to export.
   * @return SMT-LIB benchmark.
   */
  def apply( s: HOLSequent, lineWidth: Int = 80 ): ( String, Map[TBase, TBase], Map[Const, Const] ) = {
    val p = for {
      _ <- setLogic( "QF_UF" )
      _ <- declareSymbolsIn( s.elements )
      _ <- assert( s.map( identity, -_ ).elements.toList )
      _ <- checkSat
    } yield ()

    val benchmarkRecorder = new BenchmarkRecorder( lineWidth )

    benchmarkRecorder.run( p )

    ( benchmarkRecorder.getBenchmark(), benchmarkRecorder.typeRenaming.map.toMap, benchmarkRecorder.termRenaming.map.toMap )
  }
}
