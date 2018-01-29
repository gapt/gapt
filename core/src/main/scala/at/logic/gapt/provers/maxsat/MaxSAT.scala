package at.logic.gapt.provers.maxsat

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.dimacs._
import at.logic.gapt.models.PropositionalModel
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.utils.logger
import at.logic.gapt.utils.logger._

/**
 * Solver for Weighted Partial MaxSAT problems.
 */
abstract class MaxSATSolver {

  /**
   * Solves a weighted partial MaxSAT problem.
   *
   * @param hard Hard constraints in CNF.
   * @param soft Soft constraints in CNF along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solve( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): Option[DIMACS.Model]

  def solve( hard: TraversableOnce[HOLClause], soft: TraversableOnce[( HOLClause, Int )] ): Option[PropositionalModel] = {
    val encoding = new DIMACSEncoding
    debug( s"${hard.size} hard clauses with ${hard.toSeq.map( _.size ).sum} literals and ${hard.flatMap( _.elements ).toSet.size} unique variables" )
    solve(
      encoding.encodeCNF( hard ),
      soft map { case ( clause, weight ) => encoding.encodeClause( clause ) -> weight } toSeq ) map { dimacsModel =>
        encoding.decodeModel( dimacsModel )
      }
  }

  /**
   * @param hard Hard constraints.
   * @param soft Soft constraints along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solve( hard: Formula, soft: TraversableOnce[( Formula, Int )] ): Option[PropositionalModel] = {
    solve(
      logger.time( "tseitin" ) { fastStructuralCNF()( hard )._1 },
      soft.map( s => CNFp( s._1 ).map( f => ( f, s._2 ) ) ).flatten )
  }
}
