package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the subinduction required
 * to prove equal(n,n).
 */
object isaplanner38 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/isaplanner/prop_38.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allL( "h10", le"cons(n:Nat,nil:list)" )
    allL( "h7", le"n:Nat" )
    allL( "h9", le"n:Nat", le"n:Nat", le"nil" )
    eql( "h10_0", "goal" ).fromLeftToRight
    eql( "h7_0", "goal" )
    impL( "h9_0" )
    induction( hov"n:Nat", "h9_0" )
    axiomLog
    allL( "h6", le"n_0:Nat", le"n_0:Nat" )
    andL
    impL( "h6_0_1" )
    axiomLog
    axiomLog
    eql( "h9_0", "goal" )
    eql( "h7_0", "goal" ).fromLeftToRight
    refl
    // inductive case
    allL( "h11", le"x:Nat", le"xs_0:list", le"cons(n:Nat,nil:list)" )
    allL( "h8", le"n:Nat", le"x:Nat", le"xs_0:list" )
    allL( "h9", le"n:Nat", le"x:Nat", le"xs_0:list" )
    allL( "h8", le"n:Nat", le"x:Nat", le"append(xs_0:list, cons(n:Nat,nil:list))" )
    allL( "h9", le"n:Nat", le"x:Nat", le"append(xs_0:list, cons(n:Nat,nil:list))" )
    eql( "h11_0", "goal" )
    impL( "h9_0" )
    impL( "h8_0" )
    negR
    axiomLog
    eql( "h8_0", "goal" )
    impL( "h8_1" )
    negR
    axiomLog
    eql( "h8_1", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
    impL( "h9_1" )
    impL( "h8_1" )
    negR
    axiomLog
    eql( "h8_1", "goal" )
    impL( "h8_0" )
    negR
    axiomLog
    eql( "h8_0", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
    eql( "h9_1", "goal" )
    eql( "IHxs_0", "goal" )
    eql( "h9_0", "goal" ).fromLeftToRight
    refl
  }
}
