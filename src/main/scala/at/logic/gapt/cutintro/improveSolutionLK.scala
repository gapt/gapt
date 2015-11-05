package at.logic.gapt.cutintro

import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ simplify, CNFp, lcomp, instantiate }
import at.logic.gapt.proofs.resolution.{ forgetfulPropParam, forgetfulPropResolve }
import at.logic.gapt.proofs.{ RichFOLSequent, FOLClause, Sequent }
import at.logic.gapt.provers.Prover

import scala.collection.mutable

object improveSolutionLK {

  /**
   * Improves the cut-formulas in an EHS by performing forgetful resolution and paramodulation on them.
   *
   * Maintains the invariant that the cut-formulas can be realized in an LK proof.
   */
  def apply( ehs: ExtendedHerbrandSequent, prover: Prover, hasEquality: Boolean ): ExtendedHerbrandSequent = {
    val qfCutFormulas = mutable.Seq( ( ehs.cutFormulas, ehs.sehs.eigenVariables ).zipped map { instantiate( _, _ ) }: _* )

    for ( i <- qfCutFormulas.indices.reverse ) {
      val eigenVariablesInScope = for ( ( evs, j ) <- ehs.sehs.eigenVariables.zipWithIndex; ev <- evs if i < j ) yield ev
      val availableInstances = ehs.prop ++ ehs.inst filter { inst => freeVariables( inst ) subsetOf eigenVariablesInScope.toSet }
      val availableCutFormulas = for ( ( cf, j ) <- qfCutFormulas.zipWithIndex if i < j ) yield cf
      val context = availableInstances :++ availableCutFormulas
      val instances = ehs.sehs.ss( i ) match {
        case ( ev, instanceTerms ) =>
          for ( terms <- instanceTerms ) yield FOLSubstitution( ev zip terms )
      }
      qfCutFormulas( i ) = improve( context, qfCutFormulas( i ), instances toSet, prover, hasEquality )
    }

    ehs.copy( cutFormulas = ( ehs.sehs.eigenVariables, qfCutFormulas ).zipped map { All.Block( _, _ ) } )
  }

  /**
   * Improves a formula with regard to its logical complexity under the constraint that the following sequent is valid:
   *
   * instances(0)(formula) +: ... +: instances(n)(formula) +: context
   *
   * @param context  A sequent.
   * @param start  Existing solution of the constraint.
   * @param instances  List of substitutions, the intended usage are the instances of a cut-formula in an EHS.
   * @param prover  Prover to check the validity of the constraint.
   * @param hasEquality  If set to true, use forgetful paramodulation in addition to resolution.
   */
  private def improve( context: Sequent[FOLFormula], start: FOLFormula, instances: Set[FOLSubstitution], prover: Prover, hasEquality: Boolean ): FOLFormula = {
    val isSolution = mutable.Map[Set[FOLClause], Boolean]()

    def checkSolution( cnf: Set[FOLClause] ): Unit =
      if ( !isSolution.contains( cnf ) ) {
        val condition = ( for ( inst <- instances; clause <- cnf ) yield inst( clause.toFormula ) ) ++: context
        if ( prover isValid condition ) {
          isSolution( cnf ) = true
          forgetfulPropResolve( cnf ) foreach checkSolution
          if ( hasEquality ) forgetfulPropParam( cnf ) foreach checkSolution
        } else {
          isSolution( cnf ) = false
        }
      }

    checkSolution( CNFp.toClauseList( start ).map { _.distinct.sortBy { _.hashCode } }.toSet )

    val solutions = isSolution collect { case ( cnf, true ) => simplify( And( cnf map { _.toImplication } ) ) }
    solutions minBy { lcomp( _ ) }
  }

}
