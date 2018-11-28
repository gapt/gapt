package gapt.examples.induction

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object evenodd extends TacticsProof {

  ctx += InductiveType( ty"nat", hoc"0: nat", hoc"s: nat>nat" )

  ctx += hoc"even: nat>o"
  ctx += hoc"odd: nat>o"

  val proof = Lemma(
    hols"""
          even 0, ~odd 0,
          !x (even (s x) <-> ~even x),
          !x (odd (s x) <-> ~odd x)
          :-
          !x (even x <-> odd (s x))
        """ ) {
      treeGrammarInduction
        .useInterpolation
    }

}

