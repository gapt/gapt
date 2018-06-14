package gapt.examples.induction

import gapt.proofs.Context.InductiveType
import gapt.proofs.gaptic._
import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }

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

