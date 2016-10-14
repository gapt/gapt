import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p because of the subinduction,
 * in the base case of the primary induction.
 */
object isaplanner07 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_07.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // Base case
    allR
    allL( "h1", le"m:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    allL( "h3", le"Z:Nat" )
    induction( hov"m:Nat" )
    //base case
    axiomLog
    //inductive case
    allL( "h4", le"m_0:Nat" )
    axiomLog

    // Inductive case
    allR
    forget( "h0", "h1", "h3", "h4", "h6" )
    allL( "IHn_0", le"m:Nat" )
    allL( "h2", le"n_0:Nat", le"m:Nat" )
    allL( "h5", le"plus(n_0:Nat, m:Nat):Nat", le"n_0:Nat" )
    forget( "h2", "h5" )
    eql( "h2_0", "goal" )
    eql( "h5_0", "goal" )
    axiomLog

  }
}
