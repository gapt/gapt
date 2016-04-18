package at.logic.gapt.proofs.lksk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, Ant, Suc }
import org.specs2.mutable._

class LKskNewTest extends Specification {
  // Daniel's PhD thesis, p. 39
  "example 4.1.3" in {
    val p1 = Axiom( Seq( le"λx ¬S x" ), Seq( le"λx ¬S x" ), hof"S (f (λx ¬S x))" )
    val p2 = NegLeft( p1, Suc( 0 ) )
    val p3 = NegRight( p2, Ant( 0 ) )
    val p4 = ImpRight( p3, Ant( 0 ), Suc( 0 ) )
    val p5 = AllSkRight( p4, Suc( 0 ), hof"∀z (S z ⊃ ¬¬S z)", le"f: (i>o)>i", le"λY ∀z (S z ⊃ ¬Y z)" )
    val p6 = ExSkRight( p5, Suc( 0 ), hof"∃Y ∀z (S z ⊃ ¬Y z)", le"λx ¬S x" )
    val p7 = AllSkRight( p6, Suc( 0 ), hof"∀X ∃Y ∀z (X z ⊃ ¬Y z)", le"S: i>o", le"∀X ∃Y ∀z (X z ⊃ ¬Y z)" )
    p7.conclusion must_== ( Sequent() :+ ( Seq() -> hof"∀X ∃Y ∀z (X z ⊃ ¬Y z)" ) )
  }

  "and left" should {
    "require the same labels" in {
      val p1 = Axiom( Seq( le"c" ), Seq( le"d" ), hof"p" )
      val p2 = NegLeft( p1, Suc( 0 ) )
      AndLeft( p2, Ant( 0 ), Ant( 1 ) ) should throwAn[IllegalArgumentException]
    }
  }
}