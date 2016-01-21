package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object propositional {
  val A = FOLAtom( "A" )
  val B = FOLAtom( "B" )

  val lemma = Lemma(
    Sequent( Seq( "initAnt" -> Imp( A, B ) ), Seq( "initSuc" -> Or( And( A, B ), Neg( A ) ) ) )
  ) {
      orR( "initSuc" )
      negR( "initSuc_2" )
      andR( "initSuc_1" )
      axiomLog
      impL( "initAnt" )
      axiomLog
      axiomLog
    }

  val lemma2 = Lemma(
    Sequent( Seq( "initAnt" -> Imp( A, B ) ), Seq( "initSuc" -> Or( And( A, B ), Neg( A ) ) ) )
  ) {
      orR( "initSuc" )
      negR( "initSuc_2" )
      andR( "initSuc_1" )
      axiom
      impL
      axiom
      axiom
    }

  val cutTest = Lemma(
    Sequent( Seq( "a1" -> And( A, B ), "a2" -> Imp( B, A ) ), Seq( "s1" -> Or( B, A ), "s2" -> Neg( And( B, A ) ) ) )
  ) {
      cut( Imp( FOLAtom( "C" ), Bottom() ), "cfm" )
    }

  val direct = Lemma(
    Sequent( Seq( "A" -> A, "B" -> B ), Seq( "B" -> B ) )
  ) {
      axiom
    }

  val lemmaProp = Lemma(
    Sequent( Seq( "a" -> Imp( A, B ) ), Seq( "s" -> Or( And( A, B ), Neg( A ) ) ) )
  ) {
      impL
      prop
      prop
    }
}