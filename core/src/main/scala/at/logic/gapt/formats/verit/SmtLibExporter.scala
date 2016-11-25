package at.logic.gapt.formats.verit

import at.logic.gapt.expr.{ TBase, Const }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.Session._
import at.logic.gapt.provers.Session.Compilers._

object SmtLibExporter {

  /**
   *  Takes a sequent and generates the SMT-LIB benchmark as a string.
   *
   * @param s Sequent to export.
   * @return SMT-LIB benchmark.
   */
  def apply( s: HOLSequent ): ( String, Map[TBase, TBase], Map[Const, Const] ) = {
    val p = for {
      _ <- setLogic( "QF_UF" )
      _ <- declareSymbolsIn( s.elements )
      _ <- assert( s.map( identity, -_ ).elements.toList )
      _ <- checkSat
    } yield ()

    val benchmarkRecorder = new BenchmarkCompiler

    p.foldMap( benchmarkRecorder )

    ( benchmarkRecorder.getBenchmark(), benchmarkRecorder.typeRenaming.map.toMap, benchmarkRecorder.termRenaming.map.toMap )
  }
}
