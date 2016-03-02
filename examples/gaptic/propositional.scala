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
      negR( "initSuc_1" )
      andR( "initSuc_0" )
      axiomLog
      impL( "initAnt" )
      axiomLog
      axiomLog
    }

  val lemma2 = Lemma(
    Sequent( Seq( "initAnt" -> Imp( A, B ) ), Seq( "initSuc" -> Or( And( A, B ), Neg( A ) ) ) )
  ) {
      orR( "initSuc" )
      negR( "initSuc_1" )
      andR( "initSuc_0" )
      trivial
      impL
      trivial
      trivial
    }

  val direct = Lemma(
    Sequent( Seq( "A" -> A, "B" -> B ), Seq( "B" -> B ) )
  ) {
      trivial
    }

  val lemmaProp = Lemma(
    Sequent( Seq( "a" -> Imp( A, B ) ), Seq( "s" -> Or( And( A, B ), Neg( A ) ) ) )
  ) {
      impL
      prop
      prop
    }
}