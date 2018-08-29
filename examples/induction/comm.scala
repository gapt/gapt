package gapt.examples.induction

import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object comm extends TacticsProof {
  ctx += InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"
  ctx += Notation.Infix( "+", Precedence.plusMinus )

  val p = Lemma( hols"""
      p0: !x x+0 = x, 0p: !x 0+x = x,
      ps: !x!y x+s(y) = s(x+y), sp: !x!y s(x)+y = s(x+y)
      :- !x!y x+y = y+x
  """ ) {
    allR
    treeGrammarInduction
      .quantTys()
      .canSolSize( 1 )
      .useInterpolation
  }
}