import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner18 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_18.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  Lemma( sequent ) {
    allR
    induction( hov"i:Nat" )
    // Base case
    allR
    allL( "h4", le"plus(Z:Nat, m:Nat):Nat" )
    axiomLog
    // Inductive case
    allR
    allL( "IHi_0", le"m:Nat" )
    allL( "h5", le"i_0:Nat", le"plus(S(i_0:Nat):Nat, m:Nat)" )
    andL
    impL( "h5_0_1" )
    allL( "h2", le"i_0:Nat", le"m:Nat" )
    eql( "h2_0", "h5_0_1" )
    axiomLog

    axiomLog
  }
}
