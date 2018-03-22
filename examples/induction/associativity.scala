package gapt.examples.induction

import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.Context.InductiveType
import gapt.proofs.gaptic._

object associativity extends TacticsProof {
  ctx += InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"'+': nat>nat>nat"
  ctx += Notation.Infix( "+", Precedence.plusMinus )

  val p = Lemma( hols"""
      p0: !x x+0 = x, 0p: !x 0+x = x,
      ps: !x!y x+s(y) = s(x+y), sp: !x!y s(x)+y = s(x+y)
      :- !x!y!z (x+y)+z = x+(y+z)
  """ ) {
    introUnivsExcept( 2 )
    treeGrammarInduction
      .quantTys()
      .canSolSize( 1 )
  }
}