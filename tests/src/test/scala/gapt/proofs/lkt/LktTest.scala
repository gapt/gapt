package gapt.proofs.lkt

import gapt.cutintro.CutIntroduction
import gapt.examples.{ LinearExampleProof, Pi2Pigeonhole, Pi3Pigeonhole, nTape4 }
import gapt.expr.{ normalize => norm, _ }
import gapt.expr.formula.hol.containsQuantifierOnLogicalLevel
import gapt.proofs.context.Context
import gapt.proofs.lk.transformations.eliminateDefinitions
import gapt.proofs.lk.util.instanceProof
import gapt.proofs.lk.util.solvePropositional
import gapt.proofs.lk.{ LKProof, normalizeLKt }
import gapt.proofs.{ SequentMatchers, lk }
import gapt.provers.escargot.Escargot
import gapt.utils.Maybe
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
      val ( p0, lctx ) = LKToLKt( lk )
      check( p0, lctx )
      val p1 = atomizeEquality( p0, lctx )
      check( p1, lctx )
      val p2 = normalize.withDebug( p1, lctx )
      check( p2, lctx )
      p2 must beMostlyCutFree
      val p3 = LKtToLK( p2, lctx )
      p3.endSequent must beMultiSetEqual( lk.endSequent )
      ctx.foreach( _.check( p3 ) )
      ok
  }
  def beInductivelyGood( implicit ctx: Context ): Matcher[LKProof] = beLike {
    case lk =>
      val ( p0, lctx ) = LKToLKt( lk )
      check( p0, lctx )
      val p1 = atomizeEquality( p0, lctx )
      check( p1, lctx )
      val p2 = normalizeLKt.induction( p1, lctx, debugging = true )
      check( p2, lctx )
      p2 must beMostlyCutFree
      val p3 = LKtToLK( p2, lctx )
      p3.endSequent must beMultiSetEqual( lk.endSequent )
      ctx.check( p3 )
      ok
  }

  "reduce 1" in {
    val Right( l ) = solvePropositional( hos"a & (a -> b) :- ~ ~b" )
    val Right( r ) = solvePropositional( hos"~ ~b :- b" )
    lk.rules.CutRule( l, r, hof"~ ~b" ) must beGood
  }
  "fol 1" in {
    val Some( l ) = Escargot.withDeskolemization.getLKProof( hos"!x (p x -> p (s x)) :- !x (p x -> p (s (s x)))" )
    val Some( r ) = Escargot.withDeskolemization.getLKProof( hos"!x (p x -> p (s (s x))), p 0 :- p (s (s (s (s 0))))" )
    lk.rules.CutRule( l, r, hof"!x (p x -> p (s (s x)))" ) must beGood
  }
  "fol 2" in {
    CutIntroduction( LinearExampleProof( 18 ) ).get must beGood
  }
  "fol 3" in { Pi2Pigeonhole.proof must beGood }
  "fol 4" in { Pi3Pigeonhole.proof must beGood }
  "lattice" in {
    import gapt.examples.lattice._
    proof must beGood
    eliminateDefinitions( proof ) must beGood
  }
  "theory 1" in {
    import gapt.examples.theories.nat._
    addcomm.combined() must beGood
  }
  "theory 2" in {
    import gapt.examples.theories.nat._
    instanceProof( add0l.combined(), le"s 0" ) must beInductivelyGood
  }
  "theory 3" in {
    import gapt.examples.theories.nat._
    instanceProof( addcomm.combined(), le"s 0", le"s (s 0)" ) must beInductivelyGood
  }

}
