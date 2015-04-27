
package at.logic.gapt.proofs.expansionTrees

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.gapt.language.hol._
import at.logic.gapt.expr.types.{ Ti => i, To => o }

@RunWith( classOf[JUnitRunner] )
class ExpansionTreeTest extends SpecificationWithJUnit {

  val alpha = HOLVar( "\\alpha", i )
  val beta = HOLVar( "\\beta", i )
  val c = HOLConst( "c", i )
  val d = HOLConst( "d", i )
  val a = HOLConst( "a", i )
  val f = HOLConst( "f", i -> i )
  val x = HOLVar( "x", i )
  val y = HOLVar( "y", i )
  val z = HOLVar( "z", i )
  val eq = HOLConst( "=", i -> ( i -> o ) )
  val P = HOLConst( "P", i -> ( i -> ( i -> o ) ) )
  val Q = HOLConst( "Q", i -> o )
  val R = HOLConst( "R", i -> o )

  val et1 = ETWeakQuantifier(
    HOLExVar( x, HOLAtom( eq, x :: x :: Nil ) ),
    List( ( ETAtom( HOLAtom( eq, c :: c :: Nil ) ), c ) ) )

  val et2 = ETWeakQuantifier(
    HOLExVar( x, HOLAtom( P, x :: y :: c :: Nil ) ),
    List( ( ETAtom( HOLAtom( P, z :: y :: c :: Nil ) ), z ) ) )

  val et3 = ETStrongQuantifier(
    HOLAllVar( x, HOLAtom( P, x :: d :: z :: Nil ) ),
    z,
    ETAtom( HOLAtom( P, z :: d :: z :: Nil ) ) )

  val et4 = ETWeakQuantifier(
    HOLExVar( x, HOLAtom( P, x :: c :: a :: Nil ) ),
    List(
      ( ETAtom( HOLAtom( P, z :: c :: a :: Nil ) ), z ),
      ( ETAtom( HOLAtom( P, y :: c :: a :: Nil ) ), y ) ) )

  val et5 = ETImp(
    ETWeakQuantifier(
      HOLAllVar( x, HOLAtom( R, x :: Nil ) ),
      List(
        ( ETAtom( HOLAtom( R, c :: Nil ) ), c ),
        ( ETAtom( HOLAtom( R, d :: Nil ) ), d ) ) ),
    ETAnd(
      ETAtom( HOLAtom( R, c :: Nil ) ),
      ETAtom( HOLAtom( R, d :: Nil ) ) ) )

  "Expansion Trees substitution" should {

    "replace variables correctly 1" in {
      val s = HOLSubstitution( y, d )
      val etPrime = substitute( s, et2 )

      etPrime mustEqual ETWeakQuantifier(
        HOLExVar( x, HOLAtom( P, x :: d :: c :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, z :: d :: c :: Nil ) ), z ) ) )
    }

    "replace variables correctly 2" in {
      val s = HOLSubstitution( z, d )
      val etPrime = substitute( s, et2 )

      etPrime mustEqual ETWeakQuantifier(
        HOLExVar( x, HOLAtom( P, x :: y :: c :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, d :: y :: c :: Nil ) ), d ) ) )
    }

    "replace variables correctly 3" in {
      val s = HOLSubstitution( z, y )
      val etPrime = substitute( s, et3 )

      etPrime mustEqual ETStrongQuantifier(
        HOLAllVar( x, HOLAtom( P, x :: d :: y :: Nil ) ),
        y,
        ETAtom( HOLAtom( P, y :: d :: y :: Nil ) ) )
    }

    "not replace const " in {
      val s = HOLSubstitution( HOLVar( "c", i ), HOLConst( "d", i ) )
      val etPrime = substitute( s, et1 )

      etPrime mustEqual et1
    }

    "create merge node in case of collapse in weak quantifier instances " in {
      val s = HOLSubstitution( z, y )
      val etPrime = substitute.applyNoMerge( s, et4 )

      etPrime mustEqual ETWeakQuantifier(
        HOLExVar( x, HOLAtom( P, x :: c :: a :: Nil ) ),
        List(
          ( ETMerge( ETAtom( HOLAtom( P, y :: c :: a :: Nil ) ), ETAtom( HOLAtom( P, y :: c :: a :: Nil ) ) ), y ) ) )
    }
  }

  "Expansion Trees merge" should {
    "merge identical trees" in {
      merge( ETMerge( et4, et4 ) ) mustEqual et4
    }

    "do simple substitution as result of merge" in {
      val etSubst1 = ETNeg( ETStrongQuantifier( HOLAllVar( x, HOLAtom( Q, x :: Nil ) ), z, ETAtom( HOLAtom( Q, z :: Nil ) ) ) )
      val etSubst2 = ETNeg( ETStrongQuantifier( HOLAllVar( x, HOLAtom( Q, x :: Nil ) ), y, ETAtom( HOLAtom( Q, y :: Nil ) ) ) )

      // from a theoretical point of view, the result could also be equal to the second tree, but users probably expect the algo to work from left to right
      merge( ETMerge( etSubst1, etSubst2 ) ) mustEqual etSubst1
    }

    "do simple substitution as result of merge with context" in {
      val etSubst1 = ETNeg( ETStrongQuantifier( HOLAllVar( x, HOLAtom( Q, x :: Nil ) ), z, ETAtom( HOLAtom( Q, z :: Nil ) ) ) )
      val etSubst2 = ETNeg( ETStrongQuantifier( HOLAllVar( x, HOLAtom( Q, x :: Nil ) ), y, ETAtom( HOLAtom( Q, y :: Nil ) ) ) )
      merge( ETMerge( etSubst1, etSubst2 ) ) mustEqual etSubst1
    }

    "do merge with substitution in other tree of sequent triggered by merge" in {
      // example from Chaudhuri et.al : A multi-focused proof system isomorphic to expansion proofs
      val etSubst1 = ETStrongQuantifier( HOLAllVar( x, HOLAtom( R, x :: Nil ) ), z, ETAtom( HOLAtom( R, z :: Nil ) ) )
      val etSubst2 = ETStrongQuantifier( HOLAllVar( x, HOLAtom( R, x :: Nil ) ), y, ETAtom( HOLAtom( R, y :: Nil ) ) )
      val fy = HOLFunction( f, y :: Nil )
      val fz = HOLFunction( f, z :: Nil )
      val seq = ( Nil,
        // only succedent:
        ETMerge( etSubst1, etSubst2 ) ::
        ETWeakQuantifier( HOLExVar( x, HOLAtom( R, x :: Nil ) ), List(
          ( ETAtom( HOLAtom( R, fz :: Nil ) ), fz ),
          ( ETAtom( HOLAtom( R, fy :: Nil ) ), fy ) ) ) ::
        ETAtom( HOLAtom( R, z :: Nil ) ) ::
        ETAtom( HOLAtom( R, y :: Nil ) ) ::
        Nil )
      val mergedSeq = merge( seq )

      // merge will trigger a substitution y -> z

      val testResult = new ExpansionSequent( Nil,
        ( ETStrongQuantifier( HOLAllVar( x, HOLAtom( R, x :: Nil ) ), z, ETAtom( HOLAtom( R, z :: Nil ) ) ) ::
          ETWeakQuantifier( HOLExVar( x, HOLAtom( R, x :: Nil ) ), List( ( ETAtom( HOLAtom( R, fz :: Nil ) ), fz ) ) ) ::
          ETAtom( HOLAtom( R, z :: Nil ) ) ::
          ETAtom( HOLAtom( R, z :: Nil ) ) ::
          Nil ).asInstanceOf[Seq[ExpansionTree]] )

      mergedSeq mustEqual testResult
    }

  }

  "toDeep" should {
    "correctly compute the deep formula" in {
      val form = HOLImp(
        HOLAnd(
          HOLAtom( R, c :: Nil ),
          HOLAtom( R, d :: Nil ) ),
        HOLAnd(
          HOLAtom( R, c :: Nil ),
          HOLAtom( R, d :: Nil ) ) )

      val deep = toDeep( et5, 1 )

      deep mustEqual form
    }
  }

}

