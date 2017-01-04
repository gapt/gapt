package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

/**
 * This is an example used in the talk[1] at TbiLLC 2013. It generates a (cut-free) LK proof where the extracted
 * expansion tree has nested quantifiers.
 *
 * [1] http://www.illc.uva.nl/Tbilisi/Tbilisi2013/uploaded_files/inlineitem/riener.pdf
 */
object tbillc {
  val proof =
    Lemma( ( "q" -> hof"∀x (Q(x, f(x)) ∨ Q(x, g(x)))" ) +:
      ( "p" -> hof"P(a) ∨ P(b)" ) +:
      Sequent() :+ ( "pq" -> hof"∃x (P(x) ∧ ∃y Q(x, y))" ) ) {
      destruct( "p" )

      exR( le"a" ).forget; destruct( "pq" ); trivial
      allL( le"a" ).forget; destruct( "q" )
      exR( le"f a" ); trivial; exR( le"g a" ); trivial

      exR( le"b" ).forget; destruct( "pq" ); trivial
      allL( le"b" ).forget; destruct( "q" )
      exR( le"f b" ); trivial; exR( le"g b" ); trivial
    }

}
