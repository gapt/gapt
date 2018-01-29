package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.proofs.gaptic.TacticsProof
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class ExtractInductionGrammarTest extends Specification with SatMatchers {

  object example extends TacticsProof {
    import at.logic.gapt.proofs.gaptic._
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"'+': nat>nat>nat"
    val add0l = Lemma( hols"!x x+0=x, !x!y x+s(y)=s(x+y) :- !x 0+x=x" ) {
      allR; induction( hov"x:nat" ).onAll( escargot.withDeskolemization )
    }

    ctx += hoc"P: nat>nat>o"; ctx += hoc"f:nat>nat"; ctx += hoc"g:nat>nat"
    val general = Lemma( hols"!y P(0,y), !x!y (P(x,f(y))&P(x,g(y)) -> P(s(x),y)) :- !x P(x,0)" ) {
      cut( "c", hof"!x!y P(x,y)" ).right( allR andThen chain( "c" ) )
      forget( "g" ); allR; induction( hov"x:nat" ).onAll( escargot.withDeskolemization )
    }
  }
  import example._

  "add0l" in {
    val enc = InstanceTermEncoding( add0l.endSequent )
    val g = extractInductionGrammar( add0l, enc )
    val n = le"s(s(0))"
    ( enc.decodeToInstanceSequent( g.instanceLanguage( n ) ) :+ hof"0+$n=$n" ) must beEValidSequent
  }

  "general" in {
    val enc = InstanceTermEncoding( general.endSequent )
    val g = extractInductionGrammar( general, enc )
    val n = le"s(s(0))"
    ( enc.decodeToInstanceSequent( g.instanceLanguage( n ) ) :+ hof"P($n,0)" ) must beValidSequent
  }

  "prod prop 01 sip" in {
    import at.logic.gapt.examples.tip.prod.prop_01._
    val enc = InstanceTermEncoding( simpleInductionProof.endSequent )
    val g = extractInductionGrammar( simpleInductionProof )
    val n = le"S(S(0))"
    ( enc.decodeToInstanceSequent( g.instanceLanguage( n ) ) :+ hof"d $n = $n + $n" ) must beEValidSequent
  }

}
