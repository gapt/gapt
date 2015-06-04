package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansionTrees._

import scala.collection.immutable._

/**
 * Counts the number of instances of the expansion trees in a
 * MultiExpansionSequent and provides human-readable formatting of this data.
 */
object getStatistics {
  class ESStats( _1: HashMap[HOLFormula, Int], _2: HashMap[HOLFormula, Int] )
      extends Tuple2[HashMap[HOLFormula, Int], HashMap[HOLFormula, Int]]( _1, _2 ) {

    override def toString = {
      val as = _1.foldLeft( "antecedent:\n" )(
        ( str, pair ) => str + "  " + pair._1 + ": " + pair._2 + "\n" )
      val ss = _2.foldLeft( "succedent:\n" )(
        ( str, pair ) => str + "  " + pair._1 + ": " + pair._2 + "\n" )

      as + ss
    }

    /**
     * total number of instances
     */
    def total = {
      val at = _1.foldLeft( 0 )( ( n, pair ) => n + pair._2 )
      val st = _2.foldLeft( 0 )( ( n, pair ) => n + pair._2 )

      at + st
    }
  }

  def apply( mes: MultiExpansionSequent ) = {
    val a_stats = mes.antecedent.foldLeft( new HashMap[HOLFormula, Int]() )(
      ( map, met ) => map + ( met.toShallow -> met.numberOfInstances ) )
    val s_stats = mes.succedent.foldLeft( new HashMap[HOLFormula, Int]() )(
      ( map, met ) => map + ( met.toShallow -> met.numberOfInstances ) )

    new ESStats( a_stats, s_stats )
  }
}
