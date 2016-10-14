import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner12 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_12.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"n:Nat" )
    // Base case
    allR
    allL( "h5", le"map2(f,xs:list):list" )
    allL( "h5", le"xs:list" )
    eql( "h5_0", "goal" ).fromLeftToRight
    eql( "h5_1", "goal" ).fromLeftToRight
    refl
    // Inductive case
    allR
  }
}
