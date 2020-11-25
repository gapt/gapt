package gapt.examples.sequence

import gapt.expr._
import gapt.expr.formula.fol.Numeral
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.gaptic.chain
import gapt.proofs.gaptic.repeat

object SumOfOnesF2ExampleProof extends TacticsProof with ProofSequence with ExplicitEqualityTactics {
  ctx += Sort( "i" )
  ctx += hoc"s: i>i"
  ctx += hoc"0: i"
  ctx += hoc"'+': i>i>i"
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"f: i>i"

  def apply( n: Int ) =
    Proof(
      ( "trans" -> hof"∀(x:i)∀y∀z (x=y ∧ y=z → x=z)" ) +:
        ( "congplusleft" -> hof"∀x∀y∀z (y=z → y+x = z+x)" ) +:
        ( "plus1" -> hof"∀x x + s(0) = s(x)" ) +:
        ( "fs" -> hof"∀x f(s(x)) = f(x) + s(0)" ) +:
        ( "f0" -> hof"f 0 = 0" ) +:
        Sequent()
        :+ ( "goal" -> hof"f ${Numeral( n )} = ${Numeral( n )}" ) ) {
        repeat(
          explicitRewriteRight( "plus1", "goal" ) andThen
            explicitRewriteLeft( "fs", "goal" ) andThen
            chain( "congplusleft" ) )
        chain( "f0" )
      }
}
