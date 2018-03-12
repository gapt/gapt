package gapt.examples

import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.Context
import gapt.proofs.gaptic._

object Pi2Pigeonhole extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += hoc"0: i"
  ctx += hoc"s: i>i"
  ctx += hoc"M: i>i>i"
  ctx += hoc"f: i>i"
  ctx += hoc"'<=': i>i>o"
  ctx += Notation.Infix( "<=", Precedence.infixRel )

  val proof = Lemma( hols"""
      maxlt: ∀x∀y (x <= M x y  ∧  y <= M x y),
      bound: ∀x (f x = 0  ∨  f x = s 0)
      :- t: ∃x ∃y (s x <= y  ∧  f x = f y)
  """ ) {
    cut( "I0", hof"∀x ∃y (x <= y  ∧  f y = 0)" )
    cut( "I1", hof"∀x ∃y (x <= y  ∧  f y = s 0)" )

    forget( "t" ); escargot.withDeskolemization

    allL( "I1", le"0" ); decompose
    allL( "I1", le"s y" ); decompose
    forget( "I0", "I1" ); escargot

    allL( "I0", le"0" ); decompose
    allL( "I0", le"s y" ); decompose
    forget( "I0" ); escargot
  }
}

object Pi3Pigeonhole extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += hoc"0: i"
  ctx += hoc"s: i>i"
  ctx += hoc"M: i>i>i"
  ctx += hoc"f: i>i"
  ctx += hoc"'<=': i>i>o"
  ctx += Notation.Infix( "<=", Precedence.infixRel )

  val proof = Lemma( hols"""
      maxlt: ∀x∀y (x <= M x y  ∧  y <= M x y),
      bound: ∀x (f x = 0  ∨  f x = s 0)
      :- t: ∃x ∃y (s x <= y  ∧  f x = f y)
  """ ) {
    cut( "I", hof"∃z ∀x ∃y (x <= y  ∧  f y = z)" )

    exR( "I", le"0" ); exR( "I", le"s 0" )
    forget( "t", "I" ); escargot.withDeskolemization

    decompose
    allL( "I", le"0" ); decompose
    allL( "I", le"s y" ); decompose
    forget( "I" ); escargot
  }
}
