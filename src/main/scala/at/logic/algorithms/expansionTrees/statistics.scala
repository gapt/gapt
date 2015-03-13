package at.logic.algorithms.expansionTrees

import at.logic.language.hol._
import at.logic.calculi.expansionTrees._
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
  }

  def apply( mes: MultiExpansionSequent ) = {
    val a_stats = mes.antecedent.foldLeft( new HashMap[HOLFormula, Int]() )(
      ( map, met ) => map + ( met.toShallow -> met.numberOfInstances ) )
    val s_stats = mes.succedent.foldLeft( new HashMap[HOLFormula, Int]() )(
      ( map, met ) => map + ( met.toShallow -> met.numberOfInstances ) )

    new ESStats( a_stats, s_stats )
  }
}
