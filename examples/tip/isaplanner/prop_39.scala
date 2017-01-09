package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }

object isaplanner39 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_39.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val cutFormula = hof"∀xs ∀n ∀x plus(count(n, cons(x, nil)), count(n, xs)) = count(n, cons(x, xs))"

  val proofCF = Lemma(
    sequent.antecedent ++: Sequent() :+ ( "c" -> cutFormula )
  ) {
      allR
      induction( on = hov"xs:list" )
      allR
      allR
      // base case
      allL( "h9", le"n:Nat" )
      eql( "h9_0", "c" )
      allL( "h10", le"n:Nat", le"x:Nat", le"nil:list" )
      allL( "h11", le"n:Nat", le"x:Nat", le"nil:list" )
      impL( "h10_0" )
      negR
      impL( "h11_0" )
      axiomLog
      eql( "h11_0", "c" )
      eql( "h9_0", "c" ).fromLeftToRight
      allL( "h4", le"Z:Nat", le"Z:Nat" )
      allL( "h3", le"Z:Nat" )
      eql( "h4_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      refl
      allL( "h3", le"Z:Nat" )
      eql( "h10_0", "c" )
      eql( "h9_0", "c" ).fromLeftToRight
      axiomLog
      // inductive case
      allR
      allR
      allL( "h9", le"n:Nat" )
      allL( "h10", le"n:Nat", le"x:Nat", le"xs_0:list" )
      allL( "h11", le"n:Nat", le"x:Nat", le"xs_0:list" )
      impL( "h10_0" )
      negR
      impL( "h11_0" )
      axiomLog
      eql( "h11_0", "c" )
      allL( "h10", le"n:Nat", le"x_0:Nat", le"nil:list" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"nil:list" )
      impL( "h10_1" )
      negR
      impL( "h11_1" )
      axiomLog
      eql( "h11_1", "c" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "h11_2" )
      axiomLog
      eql( "h11_2", "c" )
      allL( "h4", le"Z:Nat", le"S(count(n:Nat,xs_0:list))" )
      allL( "h3", le"S(count(n:Nat,xs_0:list))" )
      eql( "h9_0", "c" )
      eql( "h4_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      eql( "h11_0", "c" ).fromLeftToRight
      refl
      allL( "h3", le"S(count(n:Nat,xs_0:list))" )
      allL( "h10", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "h10_2" )
      negR
      impL( "h11_2" )
      axiomLog
      eql( "h11_2", "c" )
      eql( "h11_0", "c" ).fromLeftToRight
      allL( "h11", le"n:Nat", le"x_0:Nat", le"nil:list" )
      impL( "h11_3" )
      axiomLog
      eql( "h11_3", "c" )
      eql( "h9_0", "c" )
      allL( "h4", le"Z:Nat", le"S(count(n:Nat,xs_0:list))" )
      eql( "h4_0", "c" )
      allL( "h3", le"S(count(n:Nat,xs_0:list))" )
      eql( "h3_1", "c" ).fromLeftToRight
      refl
      eql( "h10_1", "c" )
      eql( "h9_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      eql( "h10_2", "c" )
      eql( "h11_0", "c" ).fromLeftToRight
      refl
      eql( "h10_0", "c" )
      allL( "h10", le"n:Nat", le"x_0:Nat", le"nil:list" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"nil:list" )
      impL( "h10_1" )
      negR
      impL( "h11_1" )
      axiomLog
      eql( "h11_1", "c" )
      eql( "h9_0", "c" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "h11_2" )
      axiomLog
      eql( "h11_2", "c" )
      allL( "h4", le"Z:Nat", le"count(n:Nat,xs_0:list)" )
      allL( "h3", le"count(n:Nat,xs_0:list)" )
      eql( "h4_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      eql( "h10_0", "c" ).fromLeftToRight
      refl
      allL( "h10", le"n:Nat", le"x_0:Nat", le"cons(x:Nat, xs_0:list)" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"cons(x:Nat, xs_0:list)" )
      impL( "h11_2" )
      impL( "h10_2" )
      negR
      axiomLog
      allL( "h3", le"count(n:Nat,xs_0:list)" )
      eql( "h10_2", "c" )
      eql( "h10_1", "c" )
      eql( "h9_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      eql( "h10_0", "c" ).fromLeftToRight
      refl
      allL( "h10", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      allL( "h11", le"n:Nat", le"x_0:Nat", le"cons(x:Nat,xs_0:list)" )
      impL( "h10_3" )
      negR
      impL( "h11_3" )
      axiomLog
      allL( "h4", le"Z:Nat", le"count(n:Nat,xs_0:list)" )
      allL( "h3", le"count(n:Nat,xs_0:list)" )
      eql( "h11_2", "c" )
      impL( "h11_1" )
      axiomLog
      allL( "h4", le"Z:Nat", le"count(n:Nat,xs_0:list)" )
      allL( "h3", le"count(n:Nat,xs_0:list)" )
      eql( "h11_1", "c" )
      eql( "h9_0", "c" )
      eql( "h4_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      eql( "h10_0", "c" ).fromLeftToRight
      refl
      allL( "h3", le"count(n:Nat,xs_0:list)" )
      eql( "h10_3", "c" )
      eql( "h10_1", "c" )
      eql( "h9_0", "c" )
      eql( "h3_0", "c" ).fromLeftToRight
      eql( "h10_0", "c" ).fromLeftToRight
      refl
    }

  val proof = Lemma( sequent ) {
    cut( "c", cutFormula )
    insert( proofCF )
    allR
    allR
    allR
    allL( "c", le"xs:list", le"n:Nat", le"x:Nat" )
    axiomLog
  }

}
