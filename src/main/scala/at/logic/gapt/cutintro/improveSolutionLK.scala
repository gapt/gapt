package at.logic.gapt.cutintro

import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, lcomp, instantiate }
import at.logic.gapt.proofs.resolution.ForgetfulParamodulate
import at.logic.gapt.proofs.{ RichFOLSequent, FOLClause, Sequent }
import at.logic.gapt.provers.Prover

import scala.collection.mutable

object improveSolutionLK {

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

  private def improve( context: Sequent[FOLFormula], start: FOLFormula, instances: Set[FOLSubstitution], prover: Prover, hasEquality: Boolean ): FOLFormula = {
    val isSolution = mutable.Map[Set[FOLClause], Boolean]()

    def checkSolution( cnf: Set[FOLClause] ): Unit =
      if ( !isSolution.contains( cnf ) ) {
        val condition = ( for ( inst <- instances; clause <- cnf ) yield inst( clause.toFormula ) ) ++: context
        if ( prover isValid condition ) {
          isSolution( cnf ) = true
          for ( conseq <- forgetfulPropResolve( cnf ) ) checkSolution( conseq )
          if ( hasEquality ) for ( conseq <- ForgetfulParamodulate( cnf.toList ) ) checkSolution( conseq.toSet )
        } else {
          isSolution( cnf ) = false
        }
      }

    checkSolution( CNFp.toClauseList( start ).toSet )

    val solutions = isSolution collect { case ( sol, true ) => sol } map { cnf => And( cnf map { _.toFormula } map { toImplications( _ ) } ) }
    solutions minBy { lcomp( _ ) }
  }

  private def forgetfulPropResolve( cnf: Set[FOLClause] ) =
    for (
      clause1 <- cnf; clause2 <- cnf; if clause1 != clause2;
      atom1 <- clause1.succedent; atom2 <- clause2.antecedent; if atom1 == atom2
    ) yield cnf - clause1 - clause2 + ( clause1.removeFromSuccedent( atom1 ) ++ clause2.removeFromAntecedent( atom2 ) )

}
