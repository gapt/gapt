//package gapt.examples.schema.arithmetic

import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.proofs.context.update.{InductiveType, Sort}
import gapt.proofs.gaptic._

//TODO: theory axioms vs proof links? they are treated the same atm
//TODO: how to deal with axiom schemata that contain replacement (e.g. replacement of equal subterms)
//TODO: theory axioms are always closed formulas (i.e. don't work without quantifier rules)

object PlusLeftIdentity extends TacticsProof {
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")
  ctx += hof"1 = s 0"
  ctx += hoc"p : nat>nat"
  ctx += hoc"+ : nat>nat>nat"
  ctx += hoc"* : nat>nat>nat"

  ctx += Notation.Infix("+", Precedence.plusMinus)
  ctx += Notation.Infix("*", Precedence.timesDiv)

  ctx += "A3" -> hos":- x + 0 = x"
  ctx += "A4" -> hos":- (x + s(y) = s(x+y))"
  ctx += "Eq.1" -> le"λ(u:nat>nat) λ(x:nat) λ(y:nat) (u(x) = u(y))"
//  ctx += "Eq.1X" -> le""

  val base_case = Lemma(hos" :- 0 + 0 = 0") {
    ref("A3")
  }

}
