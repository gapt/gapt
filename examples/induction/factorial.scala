package gapt.examples.induction
import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._
import gapt.provers.prover9.Prover9
import gapt.provers.smtlib.CVC4
import gapt.provers.viper.grammars.TreeGrammarProverOptions.Passthru

object factorial extends TacticsProof {
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"fact: nat>nat"
  ctx += hoc"qfact: nat>nat>nat"

  // Problem: escargot uses fact(0) instead of s(0)...
  val qfact_correct = Lemma(
    hols"""
          om: !x s(0)*x = x,
          mo: !x x*s(0) = x,
          mc: !x!y x*y = y*x,
          mass: !x!y!z (x*y)*z = x*(y*z),
          f0: fact 0 = s(0),
          fs: !x fact (s x) = s x * fact x,
          qf0: !y qfact y 0 = y,
          qfs: !x!y qfact y (s x) = qfact (y * s x) x
          :- !x qfact (s 0) x = fact x
        """ ) {
      treeGrammarInduction
        .quantTys( TBase( "nat" ) )
        .equationalTheory( hof"x*(y*z) = (x*y)*z", hof"x*s(0) = x", hof"s(0)*x = x" )
        .canSolSize( 1 )
        .tautCheckSize( 0.5f, 1 ) // exponential blowup of canonical solution...
        .instanceProver( Prover9.extendToManySortedViaErasure )
        .smtSolver( new CVC4( "UF", Seq( "--tlimit=300" ), treatUnknownAsSat = true ) )
        .smtEquationMode( Passthru )
    }
}
