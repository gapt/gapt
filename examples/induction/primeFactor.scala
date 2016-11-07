package at.logic.gapt.examples.induction

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._

object primeFactor extends TacticsProof {
  ctx += Context.Sort( "i" )

  ctx += Const( "0", Ti )
  ctx += Const( "1", Ti )
  ctx += Const( "2", Ti )
  ctx += Const( "+", Ti -> ( Ti -> Ti ) )
  ctx += Const( "*", Ti -> ( Ti -> Ti ) )
  ctx += Const( "<", Ti -> ( Ti -> To ) )

  ctx += "div" -> le" λl λk ∃m l * m = k"
  ctx += "prime" -> le" λk (1 < k ∧ ¬∃l(div(l,k) ∧ 1 < l ∧ l < k))"

  val theoryAxioms = Seq(
    fos" :- 1 < 2",
    fos" :- n * 1 = n",
    fos" 1 < l, l < 2 :- ",
    fos" div(x, y), div(y, z) :- div(x, z)"
  )

  theoryAxioms foreach { ctx += _ }

  val theoryFormulas = theoryAxioms map { s => univclosure( s.toImplication ) }

  val ax = hof" ∀n (n = 1 ∨ prime(n) ∨ ∃l (div(l,n) ∧ 1 < l ∧ l < n))"
  def primeDiv( n: FOLTerm ) = hof"∃k ($n < 2 ∨ (div(k,$n) ∧ prime(k)))"

  val endSequent = Seq( "AX" -> ax, "IND" -> hof"∀z(z < n -> ${primeDiv( fov"z" )})" ) :- Seq( "GOAL" -> primeDiv( fov"n" ) )

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
