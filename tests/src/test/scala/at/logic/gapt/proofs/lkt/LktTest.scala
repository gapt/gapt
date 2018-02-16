package at.logic.gapt.proofs.lkt

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.{ LinearExampleProof, Pi2Pigeonhole, Pi3Pigeonhole, nTape4 }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifierOnLogicalLevel
import at.logic.gapt.proofs.lk.{ LKProof, eliminateDefinitions, solvePropositional }
import at.logic.gapt.proofs.{ Context, SequentMatchers, lk }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.Maybe
import org.specs2.matcher.Matcher
import org.specs2.mutable.Specification

class LktTest extends Specification with SequentMatchers {

  def beMostlyCutFree: Matcher[LKt] = beLike {
    case p =>
      p.subProofs.foreach {
        case Cut( f, _, _ ) =>
          require( !containsQuantifierOnLogicalLevel( f ) )
          containsQuantifierOnLogicalLevel( f ) must_== false
        case _ =>
      }
      ok
  }

  def beGood( implicit ctx: Maybe[Context] ): Matcher[LKProof] = beLike {
    case lk =>
      val ( p, lctx ) = LKToLKt( lk )
      check( p, lctx )
      val q = normalize.withDebug( p, lctx )
      check( q, lctx )
      q must beMostlyCutFree
      val lk2 = LKtToLK( q, lctx )
      lk2.endSequent must beMultiSetEqual( lk.endSequent )
      ctx.foreach( _.check( lk2 ) )
      ok
  }

  "reduce 1" in {
    val Right( l ) = solvePropositional( hos"a & (a -> b) :- ~ ~b" )
    val Right( r ) = solvePropositional( hos"~ ~b :- b" )
    lk.CutRule( l, r, hof"~ ~b" ) must beGood
  }
  "fol 1" in {
    val Some( l ) = Escargot.withDeskolemization.getLKProof( hos"!x (p x -> p (s x)) :- !x (p x -> p (s (s x)))" )
    val Some( r ) = Escargot.withDeskolemization.getLKProof( hos"!x (p x -> p (s (s x))), p 0 :- p (s (s (s (s 0))))" )
    lk.CutRule( l, r, hof"!x (p x -> p (s (s x)))" ) must beGood
  }
  "fol 2" in {
    CutIntroduction( LinearExampleProof( 18 ) ).get must beGood
  }
  "fol 3" in { Pi2Pigeonhole.proof must beGood }
  "fol 4" in { Pi3Pigeonhole.proof must beGood }
  "lattice" in {
    import at.logic.gapt.examples.lattice._
    proof must beGood
    eliminateDefinitions( proof ) must beGood
  }
  "theory 1" in {
    import at.logic.gapt.examples.theories.nat._
    addcomm.combined() must beGood
  }

}
