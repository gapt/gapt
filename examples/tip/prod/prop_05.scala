package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object prop_05 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/prod/prop_05.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lem_3 = (
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "append_one" -> hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
  )

  val lem_3_proof = Lemma( lem_3 ) {
    allR; induction( hov"xs:list" )
    //- BC
    allR
    rewrite ltr "aa1" in "append_one"
    rewrite ltr "al2" in "append_one"
    rewrite.many ltr "al1" in "append_one"
    refl
    //- IC
    allR
    rewrite ltr "aa2" in "append_one"
    rewrite.many ltr "al2" in "append_one"
    rewrite ltr "IHxs_0" in "append_one"
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "lem_3", hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
    insert( lem_3_proof )
    allR; induction( hov"x:list" )
    //- BC
    rewrite ltr "h7" in "goal"
    rewrite.many ltr "h3" in "goal"
    refl
    //- IC
    rewrite ltr "h8" in "goal"
    rewrite ltr "lem_3" in "goal"
    rewrite ltr "h4" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }
}
