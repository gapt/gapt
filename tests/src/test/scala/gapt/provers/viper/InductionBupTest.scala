package gapt.provers.viper

import gapt.expr._
import gapt.expr.hol.{ instantiate, skolemize }
import gapt.grammars.InductionGrammar
import gapt.grammars.InductionGrammar.Production
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.InductiveType
import gapt.proofs.expansion.InstanceTermEncoding
import gapt.provers.sat.Sat4j
import gapt.provers.viper.grammars.{ InductionBUP, constructSIP }
import gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class InductionBupTest extends Specification with SatMatchers {
  "lists" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti
    ctx += InductiveType( "list", hoc"nil: list", hoc"cons: i>list>list" )
    ctx += TBase( "w" )
    ctx += hoc"p: w>list>o"
    ctx += hoc"f: w>w"; ctx += hoc"g: w>w"; ctx += hoc"c: w"
    val sequent = hos"!x p x nil, !x!y!z (p (f x) y -> p (g x) y -> p x (cons z y)) :- !x p c x"
    val enc = InstanceTermEncoding( sequent )
    val tau = Var( "τ", enc.instanceTermType )
    val g = InductionGrammar(
      tau, hov"α: list",
      Map( hoc"nil" -> List(), hoc"cons" -> List( hov"ν1: i", hov"ν2: list" ) ),
      List( hov"γ: w" ),
      Vector(
        Production( tau, enc encode hof"p γ nil" ),
        Production( tau, enc encode hof"p (f γ) ν2 -> p (g γ) ν2 -> p γ (cons ν1 ν2)" ),
        Production( hov"γ:w", le"f γ" ),
        Production( hov"γ:w", le"g γ" ),
        Production( hov"γ:w", le"c" ) ) )
    ctx += hoc"a0: i"; ctx += hoc"a1: i"
    val bup = InductionBUP( g, enc, hof"p c α" )
    val solution = le"^(α:list)^ν^γ p γ ν"
    val instBup = normalize( instantiate( bup.formula, solution ) ).asInstanceOf[Formula]
    skolemize( instBup ) must beValid
    val lk = constructSIP( sequent, Vector(), bup, solution, Sat4j )( ctx.newMutable )
    ctx.check( lk )
    ok
  }

}
