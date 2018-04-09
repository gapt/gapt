package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.hol.{ containsQuantifierOnLogicalLevel, universalClosure }
import gapt.proofs._
import gapt.proofs.gaptic._
import gapt.proofs.lk.{ LKProof, cleanStructuralRules }
import gapt.provers.Prover

object constructSIP {

  /**
   * We require that `prover` can prove equationTheory from endSequent.
   */
  def apply( endSequent: HOLSequent, equationalTheory: Vector[Formula],
             bup: InductionBUP, solution: Expr, prover: Prover )( implicit ctx: MutableContext ): LKProof = {
    val g = bup.grammar
    val subst = Substitution( bup.X -> solution )
    def substF( formula: Formula ): Formula = BetaReduction.betaNormalize( subst( formula ) )

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
    state += cut( "lem", All.Block(
      nu +: g.gamma,
      BetaReduction.betaNormalize( solution( g.alpha, nu )( g.gamma: _* ) ).asInstanceOf[Formula] ) )

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
