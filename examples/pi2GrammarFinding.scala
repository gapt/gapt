import at.logic.gapt.cutintro.{ introducePi2Cut, pi2GrammarToSEHS }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.expr._
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.provers.maxsat.OpenWBO

object pi2GrammarFinding extends TacticsProof {
  ctx += Ti
  ctx += hoc"P:i>i>o"
  ctx += hoc"f:i>i"
  ctx += hoc"g:i>i"
  ctx += hoc"h:i>i"
  ctx += hoc"c:i"

  val p = Lemma( hols"h: !x (P x (f x) | P x (g x) | P x (h x)) :- ?x?y?z?w (P x y & P y z & P z w)" ) {
    cut( "c", hof"!x?y P x y" )

    forget( "g" ); decompose
    allL( "h", le"x" ).forget
    destruct( "h" )
    destruct( "h" )
    exR( le"f x" ); prop
    exR( le"g x" ); prop
    exR( le"h x" ); prop

    forget( "h" )
    allL( le"c" ); decompose
    allL( le"y" ); decompose
    allL( le"y_0" ); decompose
    exR( le"c", le"y", le"y_0", le"y_1" ).forget
    prop
  }

  val ( lang, enc ) = InstanceTermEncoding( p )

  println( s"Language:\n${lang.mkString( "\n" )}\n" )

  val stabG = stablePi2Grammar( hov"x: _Inst", hov"y", Vector( hov"z1", hov"z2", hov"z3" ), lang )

  val Some( minG ) = minimizePi2Grammar( stabG, lang, OpenWBO )

  println( s"Grammar:\n$minG\n" )

  val sehs = pi2GrammarToSEHS( minG, enc )
  println( s"SEHS:\n$sehs\n" )

  val ( Some( cutFormula ), _, _ ) = introducePi2Cut( sehs )
  println( s"Cut-formula:\n$cutFormula\n" )

}