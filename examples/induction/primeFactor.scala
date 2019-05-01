package gapt.examples.induction

import gapt.expr._
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object primeFactor extends TacticsProof {
  ctx += Sort( "i" )

  ctx += Const( "0", Ti )
  ctx += Const( "1", Ti )
  ctx += Const( "2", Ti )
  ctx += Const( "+", Ti ->: Ti ->: Ti )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += Const( "*", Ti ->: Ti ->: Ti )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Const( "<", Ti ->: Ti ->: To )
  ctx += Notation.Infix( "<", Precedence.infixRel )

  ctx += hof" div l k = (∃m l * m = k)"
  ctx += hof" prime k = (1 < k ∧ ¬∃l(div(l,k) ∧ 1 < l ∧ l < k))"

  ctx += "one_lt_two" -> fos" :- 1 < 2"
  ctx += "mul_one" -> fos" :- n * 1 = n"
  ctx += "one_lt_lt_two" -> fos" 1 < l, l < 2 :- "
  ctx += "div_trans" -> fos" div(x, y), div(y, z) :- div(x, z)"

  val ax = hof" ∀n (n = 1 ∨ prime(n) ∨ ∃l (div(l,n) ∧ 1 < l ∧ l < n))"
  def primeDiv( n: FOLTerm ) = hof"∃k ($n < 2 ∨ (div(k,$n) ∧ prime(k)))"

  val endSequent = hols"AX: $ax, IND: ∀z(z < n -> ${primeDiv( fov"z" )}) :- GOAL: ${primeDiv( fov"n" )}"

  val proof = Lemma( endSequent ) {
    allL( "AX", fov"n" ).forget
    orL

    orL

    //Case n = 1
    exR( foc"0" ).forget
    eql( "AX", "GOAL" )
    decompose
    theory

    //Case n prime
    exR( fov"n" ).forget
    orR
    forget( "GOAL_0" )
    andR right trivial
    unfold( "div" ) in "GOAL_1"
    exR( foc"1" ).forget
    theory

    //Case n composite
    decompose
    allL( "IND", fov"l" ).forget
    impL left trivial
    exL
    orL left theory
    exR( fov"k" ).forget
    decompose
    andR; theory; trivial
  }
}
