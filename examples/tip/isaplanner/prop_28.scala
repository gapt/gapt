package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

/* This is not a s.i.p because of the subinduction for equal(x,x). */
object prop_28 extends TacticsProof {

  val bench = def_prop_28.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    cut( "goal_c", hof"∀xs ∀x elem(x, append(xs, cons(x, nil)))" )
    forget( "goal" )
    allR
    induction( hov"xs:list" )
    allR
    allL( "h9", le"cons(x:Nat, nil:list):list" )
    eql( "h9_0", "goal_c" ).fromLeftToRight
    allL( "h8", le"x:Nat", le"x:Nat", le"nil:list" )
    andL
    impL( "h8_0_1" )
    orR
    induction( hov"x:Nat", "h8_0_1_0" )
    axiomLog
    allL( "h6", le"x_0:Nat", le"x_0:Nat" )
    andL( "h6_0" )
    impL( "h6_0_1" )
    axiomLog
    axiomLog
    axiomLog
    allR
    allL( "h10", le"x:Nat", le"xs_0:list", le"cons(x_0:Nat, nil:list):list" )
    eql( "h10_0", "goal_c" )
    allL( "h8", le"x_0:Nat", le"x:Nat", le"append(xs_0:list, cons(x_0:Nat, nil:list):list):list" )
    andL( "h8_0" )
    impL( "h8_0_1" )
    orR
    allL( "IHxs_0", le"x_0:Nat" )
    axiomLog
    axiomLog
    allR
    allR
    allL( "goal_c", le"xs:list", le"x:Nat" )
    axiomLog
  }
}
