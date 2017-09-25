package at.logic.gapt.examples.induction
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.provers.spass

object associativitySpecialCase extends TacticsProof {
  ctx += Context.InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"

  def tac = // FIXME(gabriel): WTF, this causes a syntax error when inlined??!?!
    treeGrammarInduction
      .equationalTheory( hof"0+x=x", hof"x+0=x" )
      .instanceProver( spass )
      .quantTys()
      .canSolSize( 2, 2 )
      .doForgetOne()

  val proof = Lemma(
    hols"""p0: !x x+0 = x, ps: !x!y x+s(y) = s(x+y),
           0p: !x 0+x = x, sp: !x!y s(x)+y = s(x+y)
           :- !x (x+x)+x = x+(x+x) """ ) {
      tac
    }
}
