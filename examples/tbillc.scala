package gapt.examples

import gapt.expr._
import gapt.proofs.context.Context.Sort
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

/**
 * This is an example used in the talk[1] at TbiLLC 2013. It generates a (cut-free) LK proof where the extracted
 * expansion tree has nested quantifiers.
 *
 * [1] http://www.illc.uva.nl/Tbilisi/Tbilisi2013/uploaded_files/inlineitem/riener.pdf
 */
object tbillc extends TacticsProof {
  ctx += Sort( "i" )
  ctx += hoc"Q: i>i>o"
  ctx += hoc"P: i>o"
  ctx += hoc"f: i>i"
  ctx += hoc"g: i>i"
  ctx += hoc"a: i"
  ctx += hoc"b: i"

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
