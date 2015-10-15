package at.logic.gapt.provers.maxsat

import java.io._

import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.formats.dimacs._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.utils.logging.metrics
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.{ withTempFile, runProcess }

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

  def solve( hard: TraversableOnce[HOLClause], soft: TraversableOnce[( HOLClause, Int )] ): Option[Interpretation] = {
    val encoding = new DIMACSEncoding
    solve(
      encoding.encodeCNF( hard ),
      soft map { case ( clause, weight ) => encoding.encodeClause( clause ) -> weight } toSeq
    ) map { dimacsModel =>
        encoding.decodeModel( dimacsModel )
      }
  }

  /**
   * @param hard Hard constraints.
   * @param soft Soft constraints along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solve( hard: HOLFormula, soft: TraversableOnce[( HOLFormula, Int )] ): Option[Interpretation] = {
    solve(
      metrics.time( "tseitin" ) { TseitinCNF( hard.asInstanceOf[FOLFormula] ) },
      soft.map( s => CNFp.toClauseList( s._1 ).map( f => ( f, s._2 ) ) ).flatten
    )
  }
}

abstract class ExternalMaxSATSolver extends MaxSATSolver with ExternalProgram {
  def command: Seq[String]

  protected def runProgram( dimacsInput: String ): String =
    withTempFile.fromString( dimacsInput ) { inFile =>
      runProcess.withExitValue( command :+ inFile )._2
    }

  def solve( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): Option[DIMACS.Model] =
    readWDIMACS( runProgram( writeWDIMACS( hard, soft ) ) )

  val isInstalled =
    try solve( FOLAtom( "p" ), Seq( -FOLAtom( "p" ) -> 10 ) ).isDefined
    catch { case _: IOException => false }
}
