package at.logic.gapt.proofs.ceres

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.formats.llk._
import at.logic.gapt.proofs.SequentMatchers
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.proofs.{ Context, Sequent, gaptic }
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.proofs.lk.{ CutRule, ReductiveCutElimination }
import org.specs2.mutable._

class CeresTest extends Specification with SequentMatchers {

  def load( file: String, pname: String ) =
    LLKProofParser( ClasspathInputFile( file ) ).proof( pname )

  "Struct extraction" should {
    "work for the permutation proof" in {
      val proof = load( "perm.llk", "TheProof" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }

    "work for simple equations (1)" in {
      val proof = load( "eqsimple.llk", "Proof1" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
    "work for simple equations (2)" in {
      val proof = load( "eqsimple.llk", "Proof2" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
    "work for simple equations (3)" in {
      val proof = load( "eqsimple.llk", "Proof3" )
      val acnf = CERES( proof, Escargot )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
  }

  "a simple intuitionistic proof" in {
    val proof = simple.fol2.proof
    val acnf = ReductiveCutElimination( CERES( proof ) )
    acnf.endSequent must beMultiSetEqual( proof.endSequent )
  }

  "many-sorted proofs" in {
    import gaptic._
    val p = Lemma( Sequent() :+ ( "goal" ->
      hof"P(0:nat) & !x (P x -> P (s x)) -> P(s(s(s(s(0)))))" ) ) {

      cut( "lem", hof"!x (P(x:nat) -> P (s (s x)))" ) onAll decompose
      repeat( chain( "goal_0_1" ) ); trivial
      repeat( chain( "lem" ) ); trivial
    }

    CERES( p, Escargot ).conclusion must beMultiSetEqual( p.conclusion )
  }

  "second-order definitions" in {
    implicit var ctx = Context()
    ctx += Context.Sort( "i" )
    ctx += hof"in x X = (X x: o)"
    ctx ++= Seq( hoc"P:i>i>o", hoc"c:i", hoc"f:i>i", hoc"g:i>i" )
    ctx += hof"Q x = (∃y P x y)"

    import gaptic._
    val p = Lemma(
      ( "pc" -> hof"∀y P(c, y)" ) +: ( "pf" -> hof"∀x ∀y (P(x, g y) ⊃ P(f x, y))" ) +:
        Sequent()
        :+ ( "goal" -> hof"in(f(f(f(f(c)))), Q)" )
    ) {
        cut( "cut", hof"∀x ∀y (P(x, g(g y)) ⊃ P(f(f x), y))" ); forget( "goal" )
        decompose; repeat( chain( "pf" ) ); trivial

        repeat( unfold( "in", "Q" ) in "goal" )
        exR( le"c" ).forget
        repeat( chain( "cut" ) ); chain( "pc" )
      }

    CERES( p, Escargot ).conclusion must beMultiSetEqual( p.conclusion )
  }

  "work for the example in issue 555" in {
    val Some( proof ) = Escargot.getLKProof( hos"f 0 = t, !x (f (s x) = f x) :- f ${Numeral( 9 )} = t" )
    val Some( proofWithCut ) = CutIntroduction( proof )
    val acnf = CERES( proofWithCut )
    for ( CutRule( p1, a1, p2, a2 ) <- acnf.subProofs ) isAtom( p1.endSequent( a1 ) ) must beTrue
    ok
  }

}
