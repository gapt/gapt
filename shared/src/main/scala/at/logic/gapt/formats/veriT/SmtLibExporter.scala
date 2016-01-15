package at.logic.gapt.formats.veriT

import at.logic.gapt.expr.{ TBase, Const }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.smtlib.BenchmarkRecordingSession

object SmtLibExporter {

  /**
   *  Takes a sequent and generates the SMT-LIB benchmark as a string.
   *
   * @param s Sequent to export.
   * @return SMT-LIB benchmark.
   */
  def apply( s: HOLSequent ): ( String, Map[TBase, TBase], Map[Const, Const] ) =
    for ( session <- new BenchmarkRecordingSession ) yield {
      session setLogic "QF_UF"
      session declareSymbolsIn s.elements
      s.map( identity, -_ ) foreach session.assert
      session.checkSat()
      ( session.getBenchmark(), session.typeRenaming.map.toMap, session.termRenaming.map.toMap )
    }
}
