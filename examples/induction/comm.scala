package at.logic.gapt.examples.induction

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ Notation, Precedence }
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.gaptic._

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
  }
}