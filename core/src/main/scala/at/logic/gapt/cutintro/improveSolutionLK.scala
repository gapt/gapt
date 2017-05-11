package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, instantiate, lcomp, simplify }
import at.logic.gapt.proofs.resolution.{ forgetfulPropParam, forgetfulPropResolve }
import at.logic.gapt.proofs.{ FOLClause, RichFOLSequent, Sequent }
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.Session._
import cats.implicits._

import scala.collection.mutable

object improveSolutionLK {

  /**
   * Improves the cut-formulas in an EHS by performing forgetful resolution and paramodulation on them.
   *
   * Maintains the invariant that the cut-formulas can be realized in an LK proof.
   */
  def apply( ehs: SolutionStructure, prover: Prover, hasEquality: Boolean,
             forgetOne:    Boolean = false,
             minimizeBack: Boolean = false ): SolutionStructure = {
    val formulasInImprovement = ehs.formulas.to[mutable.Seq]

    for ( i <- formulasInImprovement.indices.reverse ) {
      val eigenVariablesInScope = for ( ( evs, j ) <- ehs.sehs.eigenVariables.zipWithIndex; ev <- evs if i < j ) yield ev
      val availableInstances = ehs.endSequentInstances filter { inst => freeVariables( inst ) subsetOf eigenVariablesInScope.toSet }
      val availableCutFormulas = for ( ( cf, j ) <- formulasInImprovement.zipWithIndex if i < j ) yield cf
      val context = availableInstances :++ availableCutFormulas
      val instances = ehs.sehs.ss( i ) match {
        case ( ev, instanceTerms ) =>
          for ( terms <- instanceTerms ) yield FOLSubstitution( ev zip terms )
      }
      formulasInImprovement( i ) = improve( context, formulasInImprovement( i ), instances toSet, prover, hasEquality, forgetOne )
    }

    if ( minimizeBack && formulasInImprovement.size == 1 ) {
      formulasInImprovement( 0 ) = improveBack( ehs.endSequentInstances, formulasInImprovement( 0 ), prover )
    }

    ehs.copy( formulas = formulasInImprovement )
  }

  /**
   * Improves a formula with regard to its logical complexity by taking consequences under the constraint that the following sequent is valid:
   *
   * instances(0)(formula) +: ... +: instances(n)(formula) +: context
   *
   * @param context  A sequent.
   * @param start  Existing solution of the constraint.
   * @param instances  List of substitutions, the intended usage are the instances of a cut-formula in an EHS.
   * @param prover  Prover to check the validity of the constraint.
   * @param hasEquality  If set to true, use forgetful paramodulation in addition to resolution.
   */
  private def improve( context: Sequent[FOLFormula], start: FOLFormula, instances: Set[FOLSubstitution], prover: Prover,
                       hasEquality: Boolean, forgetOne: Boolean ): FOLFormula = {
    val names = containedNames( instances ) ++ containedNames( start ) ++ containedNames( context.elements )
    val nameGen = rename.awayFrom( names )
    val grounding = Substitution( for ( v <- freeVariables( start +: context.elements ) ++ instances.flatMap( _.range ) )
      yield v -> Const( nameGen.fresh( v.name ), v.ty ) )
    val groundInstances = instances.map( grounding.compose )
    val isSolution = mutable.Map[Set[FOLClause], Boolean]()

    def checkSolution( cnf: Set[FOLClause] ): Session[Unit] = when( !isSolution.contains( cnf ) ) {
      val clauses = for ( inst <- groundInstances; clause <- cnf ) yield inst( clause.toDisjunction )

      withScope( assert( clauses.toList ) >> checkUnsat ).flatMap { isSol =>
        isSolution( cnf ) = isSol

        when( isSol ) {
          forgetfulPropResolve( cnf ).toList.traverse_( checkSolution ) >>
            when( hasEquality ) { forgetfulPropParam( cnf ).toList.traverse_( checkSolution ) } >>
            when( forgetOne ) { cnf.toList.traverse_( c => checkSolution( cnf - c ) ) }
        }
      }
    }

    prover.runSession {
      declareSymbolsIn( names ++ containedNames( grounding ) ) >>
        assert( grounding( context.toNegConjunction ) ) >>
        checkSolution( CNFp( start ).map { _.distinct.sortBy { _.hashCode } } )
    }

    val solutions = isSolution collect {
      case ( cnf, true ) => simplify( And( cnf map { _.toImplication } ) )
    }
    solutions minBy { lcomp( _ ) }
  }

  /**
   * Improves a formula with regard to its logical complexity by taking backwards consequences under the constraint that the following sequent is valid:
   *
   * context :+ formula
   *
   * @param context  A sequent.
   * @param start  Existing solution of the constraint.
   * @param prover  Prover to check the validity of the constraint.
   */
  private def improveBack( context: Sequent[FOLFormula], start: FOLFormula, prover: Prover ): FOLFormula =
    simplify( And( CNFp( start ) map { improveBack( context, _, prover ).toImplication } ) )

  private def improveBack( context: Sequent[FOLFormula], start: FOLClause, prover: Prover ): FOLClause = {
    val isSolution = mutable.Map[FOLClause, Boolean]()

    def checkSolution( clause: FOLClause ): Unit =
      if ( !isSolution.contains( clause ) ) {
        val condition = context :+ clause.toDisjunction
        if ( prover isValid condition ) {
          isSolution( clause ) = true
          for ( a <- clause.indices ) checkSolution( clause delete a )
        } else {
          isSolution( clause ) = false
        }
      }

    checkSolution( start )

    isSolution collect { case ( clause, true ) => clause } minBy { _.size }
  }

}
