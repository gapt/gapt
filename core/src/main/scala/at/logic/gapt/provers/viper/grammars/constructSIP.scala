package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ containsQuantifierOnLogicalLevel, universalClosure }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, cleanStructuralRules }
import at.logic.gapt.provers.Prover

object constructSIP {

  /**
   * We require that `prover` can prove equationTheory from endSequent.
   */
  def apply( endSequent: HOLSequent, equationalTheory: Vector[Formula],
             bup: InductionBUP, solution: Expr, prover: Prover )( implicit ctx: MutableContext ): LKProof = {
    val g = bup.grammar
    val subst = Substitution( bup.X -> solution )
    def substF( formula: Formula ): Formula = normalize( subst( formula ) ).asInstanceOf[Formula]

    val nu = rename( Var( "ν", g.indTy ), containedNames( bup.formula ) ++ containedNames( solution ) )

    var state = ProofState( endSequent )

    for ( ( eq, i ) <- equationalTheory.zipWithIndex ) {
      val lem = universalClosure( eq )
      state += cut( s"eq_$i", lem )
      state += forget( "g" )
      state += decompose
      state += resolutionProver( prover ).quiet
    }

    state += allR( g.alpha )
    state += cut( "lem", All.Block( nu +: g.gamma, normalize( solution( g.alpha, nu )( g.gamma: _* ) ).asInstanceOf[Formula] ) )

    state += forget( "g" )
    state += allR( nu )
    val Some( ctrs ) = ctx.getConstructors( g.indTy )
    state += induction( nu ).withEigenVariables( Map() ++ ( for ( ctr <- ctrs ) yield ctr -> g.nus( ctr ).toVector ) )
    for ( ctr <- ctrs ) {
      val Some( bupCase ) = bup.indCases.find( _.constructor == ctr )
      for ( g <- g.gamma ) state += allR( g )
      state += haveInstances( bupCase.theoryFormulas )
      state += haveInstances( bupCase.indHyps.map( substF ) :- Nil )
      state += haveInstance( substF( bupCase.indConcl ), Polarity.InSuccedent )
      state += forget( ( l, f ) => !l.startsWith( "eq_" ) && containsQuantifierOnLogicalLevel( f ) )
      state += resolutionProver( prover ).quiet
    }

    state += haveInstances( bup.endCut.theoryFormulas )
    state += haveInstances( bup.endCut.indFormulaInstances.map( substF ) :- Nil )
    state += forget( ( l, f ) => !l.startsWith( "eq_" ) && containsQuantifierOnLogicalLevel( f ) )
    state += resolutionProver( prover )

    cleanStructuralRules( state.result )
  }

}
