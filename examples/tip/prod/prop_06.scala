package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object prop_06 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/prod/prop_06.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val theory = sequent.antecedent ++: Sequent()

  val lem_2 = (
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "append_left_cons" -> hof"∀xs∀y∀zs length(append(xs,cons(y,zs))) = S(length(append(xs,zs)))" )
  )

  val lem_2_proof = Lemma( lem_2 ) {
    allR; induction( hov"xs:list" )
    //- BC
    decompose
    rewrite.many ltr "aa1" in "append_left_cons"
    rewrite.many ltr "al2" in "append_left_cons"
    refl
    //- IC
    decompose
    rewrite.many ltr "aa2" in "append_left_cons"
    rewrite.many ltr "al2" in "append_left_cons"
    rewrite.many ltr "IHxs_0" in "append_left_cons"
    refl
  }

  val lem_3 = (
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "append_one" -> hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
  )

  val lem_3_proof = Lemma( lem_3 ) {
    cut( "lem_2", hof"∀xs∀y∀zs length(append(xs,cons(y,zs))) = S(length(append(xs,zs)))" )
    insert( lem_2_proof )
    decompose
    rewrite ltr "lem_2" in "append_one"
    induction( hov"xs:list" )
    //- BC
    rewrite ltr "aa1" in "append_one"
    rewrite.many ltr "al1" in "append_one"
    refl
    //- IC
    rewrite ltr "aa2" in "append_one"
    rewrite.many ltr "al2" in "append_one"
    rewrite ltr "IHxs_0" in "append_one"
    refl
  }

  val prop_05 = (
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "ar1" -> hof"rev(nil) = nil" ) +:
    ( "ar2" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    Sequent() :+ ( "length_rev_inv" -> hof"∀x length(rev(x)) = length(x)" )
  )

  val prop_05_proof = Lemma( prop_05 ) {
    cut( "lem_3", hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
    insert( lem_3_proof )
    allR; induction( hov"x:list" )
    //- BC
    rewrite ltr "ar1" in "length_rev_inv"
    refl
    //- IC
    rewrite ltr "ar2" in "length_rev_inv"
    rewrite ltr "lem_3" in "length_rev_inv"
    rewrite ltr "al2" in "length_rev_inv"
    rewrite ltr "IHx_0" in "length_rev_inv"
    refl
  }

  val proof = Lemma( sequent ) {
    allR; induction( hov"x:list" )
    //- BC
    allR
    rewrite ltr "h7" in "goal"
    rewrite ltr "h5" in "goal"
    rewrite ltr "h3" in "goal"
    cut( "prop_05", hof"∀x length(rev(x)) = length(x)" )
    insert( prop_05_proof )
    rewrite ltr "prop_05" in "goal"
    refl
    //- IC
    decompose
    rewrite ltr "h8" in "goal"
    rewrite ltr "h10" in "goal"
    rewrite ltr "h6" in "goal"
    rewrite ltr "h4" in "goal"
    cut( "lem_3", hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
    insert( lem_3_proof )
    rewrite ltr "lem_3" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }
}
