package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ instantiate, skolemize }
import at.logic.gapt.grammars.InductionGrammar
import at.logic.gapt.grammars.InductionGrammar.Production
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.MutableContext
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.viper.grammars.{ InductionBUP, constructSIP }
import at.logic.gapt.utils.SatMatchers
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
