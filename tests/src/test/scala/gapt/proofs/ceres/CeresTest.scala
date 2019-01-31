package gapt.proofs.ceres

import gapt.cutintro.CutIntroduction
import gapt.examples._
import gapt.expr._
import gapt.expr.fol.Numeral
import gapt.expr.hol.isAtom
import gapt.formats.ClasspathInputFile
import gapt.formats.llk._
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.CutRule
import gapt.proofs.lk.transformations.cutNormal
import gapt.proofs.{ Sequent, SequentMatchers, gaptic }
import gapt.provers.escargot.Escargot
import gapt.utils.SatMatchers
import org.specs2.mutable._

class CeresTest extends Specification with SequentMatchers with SatMatchers {

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
    val proof = fol2.proof
    val acnf = cutNormal( CERES( proof ) )
    acnf.endSequent must beMultiSetEqual( proof.endSequent )
  }

  "many-sorted proofs" in {
    import gaptic._
    val p = Proof( Sequent() :+ ( "goal" ->
      hof"P(0:nat) & !x (P x -> P (s x)) -> P(s(s(s(s(0)))))" ) ) {

      cut( "lem", hof"!x (P(x:nat) -> P (s (s x)))" ) onAll decompose
      repeat( chain( "goal_0_1" ).at( "lem_1" ) ); trivial
      repeat( chain( "lem" ) ); trivial
    }

    CERES( p, Escargot ).conclusion must beMultiSetEqual( p.conclusion )
  }

  "second-order definitions" in {
    implicit val ctx = MutableContext.default()
    ctx += Sort( "i" )
    ctx += hof"in (x:i) X = (X x: o)"
    ctx ++= Seq( hoc"P:i>i>o", hoc"c:i", hoc"f:i>i", hoc"g:i>i" )
    ctx += hof"Q x = (∃y P x y)"

    import gaptic._
    val p = Lemma(
      ( "pc" -> hof"∀y P(c, y)" ) +: ( "pf" -> hof"∀x ∀y (P(x, g y) → P(f x, y))" ) +:
        Sequent()
        :+ ( "goal" -> hof"in(f(f(f(f(c)))), Q)" ) ) {
        cut( "cut", hof"∀x ∀y (P(x, g(g y)) → P(f(f x), y))" ); forget( "goal" )
        decompose; repeat( chain( "pf" ) ); trivial

        unfold( "in", "Q" ) in "goal"
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

  "extraction of expansions from projections" should {
    "work for simple fol proofs" in {
      val p = fol1.proof
      val e = CERES.expansionProof( p, prover = Escargot )
      e.deep must beValidSequent
    }

    "work for proofs with equality" in {
      val p = Pi2Pigeonhole.proof
      val e = CERES.expansionProof( p, prover = Escargot )
      e.deep must beEValidSequent
    }
  }
}
