package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }

/* This proof is not a s.i.p. because of the subinduction on xs */
object isaplanner41 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_41.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val cutFormula = hof"∀n ∀xs ∀f take(n, map2(f, xs)) = map2(f, take(n, xs))"

  val proofCF = Lemma( sequent.antecedent ++: Sequent() :+ ( "c" -> cutFormula ) ) {
    allR
    induction( on = hov"n:Nat" )
    allR
    allR
    allL( "h3", le"xs:list" )
    allL( "h3", le"map2(f,xs:list)" )
    allL( "h6", le"f:fun1" )
    eql( "h3_0", "c" )
    eql( "h3_1", "c" ).fromLeftToRight
    eql( "h6_0", "c" ).fromLeftToRight
    refl
    allR
    induction( on = hov"xs:list" )
    allR
    allL( "h6", le"f:fun1" )
    allL( "h4", le"n_0:Nat" )
    eql( "h4_0", "c" ).fromLeftToRight
    eql( "h6_0", "c" ).fromLeftToRight
    eql( "h4_0", "c" ).fromLeftToRight
    refl
    allR
    allL( "h7", le"f:fun1", le"x:sk", le"xs_0:list" )
    allL( "h7", le"f:fun1", le"x:sk", le"take(n_0,xs_0)" )
    allL( "h5", le"n_0:Nat", le"apply1(f,x:sk)", le"map2(f,xs_0:list)" )
    allL( "h5", le"n_0:Nat", le"x:sk", le"xs_0:list" )
    allL( "IHn_0", le"xs_0:list", le"f:fun1" )
    eql( "h7_0", "c" )
    eql( "h5_0", "c" )
    eql( "h5_1", "c" )
    eql( "h7_1", "c" )
    eql( "IHn_0_0", "c" ).fromLeftToRight
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "c", cutFormula )
    insert( proofCF )
    allR
    allR
    allR
    allL( "c", le"n:Nat", le"xs:list", le"f:fun1" )
    axiomLog
  }
}
