package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.sequentialInductionAxioms

object isaplanner03 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_03.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val cutFormula = hof"∀xs ∀ys ∀n le(count(n, xs), count(n, append(xs, ys)))"
  val proofCutFormula = Lemma( sequent.antecedent ++: Sequent() :+ ( "goal" -> cutFormula ) ) {
    allR
    induction( hov"xs:list" )
    allR
    allR
    allL( "h10", le"n:Nat" )
    allL( "h3", le"count(n:Nat, append(nil, ys:list))" )
    eql( "h10_0", "goal" )
    axiomLog
    allR
    allR
    allL( "h14", le"x:Nat", le"xs_0:list", le"ys:list" )
    eql( "h14_0", "goal" )
    allL( "h11", le"n:Nat", le"x:Nat", le"xs_0:list" )
    impL( "h11_0" )
    negR( "h11_0" )
    allL( "h12", le"n:Nat", le"x:Nat", le"xs_0:list" )
    impL( "h12_0" )
    axiomLog
    allL( "h12", le"n:Nat", le"x:Nat", le"append(xs_0:list, ys:list)" )
    impL
    axiomLog
    eql( "h12_0", "goal" )
    eql( "h12_1", "goal" )
    allL( "h5", le"count(n:Nat, xs_0:list)", le"count(n:Nat, append(xs_0:list, ys:list))" )
    allL( "IHxs_0", le"ys:list", le"n:Nat" )
    andL( "h5_0" )
    impL( "h5_0_1" )
    axiomLog
    axiomLog
    allL( "h11", le"n:Nat", le"x:Nat", le"append(xs_0:list, ys:list)" )
    impL( "h11_1" )
    negR
    allL( "h12", le"n:Nat", le"x:Nat", le"xs_0:list" )
    allL( "h12", le"n:Nat", le"x:Nat", le"append(xs_0:list, ys:list)" )
    impL( "h12_0" )
    axiomLog
    impL( "h12_1" )
    axiomLog
    eql( "h12_0", "goal" )
    eql( "h12_1", "goal" )
    allL( "h5", le"count(n:Nat, xs_0:list)", le"count(n:Nat, append(xs_0:list, ys:list))" )
    andL( "h5_0" )
    allL( "IHxs_0", le"ys:list", le"n:Nat" )
    impL( "h5_0_1" )
    axiomLog
    axiomLog
    eql( "h11_0", "goal" )
    eql( "h11_1", "goal" )
    allL( "IHxs_0", le"ys:list", le"n:Nat" )
    axiomLog
  }

  val proof = Lemma( sequent ) {
    cut( "CF", cutFormula )
    insert( proofCutFormula )
    allR
    allR
    allR
    allL( "CF", le"xs:list", le"ys:list", le"n:Nat" )
    axiomLog
  }

  val inductionAxiom = sequentialInductionAxioms.inductionAxioms( sequent.succedent.head._2, List( hov"xs:list" ) ).valueOr( es => throw new Exception( es.head ) ).head
  val proof2 = Lemma( ( "IAxs_0" -> inductionAxiom ) +: sequent ) {
    escargot
  }
}
