package gapt.examples

import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

/**
 * Formalisation of the tape-proof as described in C. Urban: Classical Logic
 * and Computation, PhD Thesis, Cambridge University, 2000.
 */
object tapeUrban extends TacticsProof {
  ctx += Sort( "i" )

  ctx += hoc"f: i>i"
  ctx += hoc"'<=': i>i>o"
  ctx += hoc"'<': i>i>o"
  ctx += hoc"max: i>i>i"
  ctx += hoc"s: i>i"
  ctx += hoc"0: i"
  ctx += hof"1 = s 0"

  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += Notation.Infix( "<", Precedence.infixRel )

  ctx += hof"A = (∀x (f(x)=0 ∨ f(x)=1))"
  ctx += hof"P = (∃n ∃m (n < m ∧ f(n) = f(m)))"
  ctx += hof"T = (∀i ∀x ∀y (f(y) = i ∧ f(x) = i → f(x) = f(y)))"
  ctx += hof"S = (∀x ∀y (s x <= y → x < y))"
  ctx += hof"M_1 = (∀y ∀x x <= max x y)"
  ctx += hof"M_2 = (∀y ∀x y <= max x y)"
  ctx += hof"I i = (∀n ∃k (n <= k ∧ f(k) = i))"

  val tau = Lemma(
    ( "M_1" -> hof"M_1" ) +: ( "M_2" -> hof"M_2" ) +: ( "A" -> hof"A" ) +:
      Sequent() :+ ( "I0" -> hof"I 0" ) :+ ( "I1" -> hof"I 1" ) ) {
      unfold( "I" ) in "I1"
      allR( "I1", fov"n_" )
      unfold( "I" ) in "I0"
      allR( "I0", fov"n" )
      exR( "I0", le"max n n_" )
      exR( "I1", le"max n n_" )
      forget( "I0", "I1" )
      andR( "I1_0" )
      forget( "A", "M_1", "I0_0" )
      unfold( "M_2" ) in "M_2"
      chain( "M_2" )

      andR( "I0_0" )
      forget( "A", "M_2", "I1_0" )
      unfold( "M_1" ) in "M_1"
      chain( "M_1" )

      forget( "M_1", "M_2" )
      unfold( "A" ) in "A"
      allL( "A", le"max n n_" )
      prop
    }

  val epsilon_i = Lemma(
    ( "Ii" -> hof"I i" ) +: ( "S" -> hof"S" ) +: ( "T" -> hof"T" ) +:
      Sequent() :+ ( "P" -> hof"P" ) ) {
      unfold( "I" ) in "Ii"
      allL( "Ii", le"0" )
      exL( "Ii_0", fov"n" )
      allL( "Ii", le"s n" )
      exL( "Ii_1", fov"m" )
      forget( "Ii" )
      unfold( "P" ) in "P"
      exR( "P", fov"n", fov"m" )
      forget( "P" )
      andL( "Ii_0" )
      andL( "Ii_1" )
      forget( "Ii_0_0" )
      andR( "P_0" )
      by {
        forget( "Ii_1_1", "Ii_0_1", "T" )
        unfold( "S" ) in "S"
        chain( "S" )
        trivial
      }
      by {
        forget( "Ii_1_0", "S" )
        unfold( "T" ) in "T"
        chain( "T" )
        trivial
        trivial
      }
    }

  val sigma = Lemma(
    ( "M_1" -> hof"M_1" ) +: ( "M_2" -> hof"M_2" ) +: ( "S" -> hof"S" ) +: ( "T" -> hof"T" ) +: ( "A" -> hof"A" ) +:
      Sequent() :+ ( "P" -> hof"P" ) ) {
      cut( "I0", hof"I 0" ) left by {
        cut( "I1", hof"I 1" ) left insert( tau )
        insert( epsilon_i )
      }
      insert( epsilon_i )
    }

  val proof = sigma
}

