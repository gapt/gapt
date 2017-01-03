package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

object prop_01 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/prod/prop_01.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    cut( "lem", hof"!x !y plus(x, S(y)) = S(plus(x, y))" ); forget( "goal" )
    allR; allR
    induction( hov"x:Nat" )
    rewrite.many ltr "h1" in "lem"; refl // IB
    rewrite.many ltr ( "h2", "IHx_0" ) in "lem"; refl // IS

    allR
    induction( hov"x:Nat" )
    rewrite.many ltr ( "h1", "h3" ) in "goal"; refl // IB
    rewrite.many ltr ( "h2", "h4", "lem" ) in "goal"; quasiprop // IS
  }
}
