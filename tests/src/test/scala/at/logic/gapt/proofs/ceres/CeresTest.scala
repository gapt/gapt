package at.logic.gapt.proofs.ceres

import at.logic.gapt.formats.llkNew._
import at.logic.gapt.proofs.SequentMatchers
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent, gaptic }
import at.logic.gapt.expr._
import org.specs2.mutable._

import scala.io.Source

/**
 * Created by marty on 11/24/15.
 */
class CeresTest extends Specification with SequentMatchers {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  def load( file: String, pname: String ) =
    LLKProofParser.parseString( Source fromInputStream getClass.getClassLoader.getResourceAsStream( file ) mkString ).proof( pname )

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
      skipped( "produces an error" ) //TODO: fix the error!
      checkForProverOrSkip

      val proof = load( "eqsimple.llk", "Proof3" )
      val acnf = CERES( proof )
      acnf.endSequent must beMultiSetEqual( proof.endSequent )
    }
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
    implicit var ctx = FiniteContext()
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

        unfold( "goal", "in", "Q" )
        exR( le"c" ).forget
        repeat( chain( "cut" ) ); chain( "pc" )
      }

    CERES( p, Escargot ).conclusion must beMultiSetEqual( p.conclusion )
  }

}
