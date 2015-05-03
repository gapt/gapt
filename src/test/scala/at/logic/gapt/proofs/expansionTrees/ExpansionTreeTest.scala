
package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.language.hol.HOLSubstitution
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.gapt.expr._
import at.logic.gapt.expr.types.{ Ti => i, To => o }

@RunWith( classOf[JUnitRunner] )
class ExpansionTreeTest extends SpecificationWithJUnit {

  val alpha = Var( "\\alpha", i )
  val beta = Var( "\\beta", i )
  val c = Const( "c", i )
  val d = Const( "d", i )
  val a = Const( "a", i )
  val f = Const( "f", i -> i )
  val x = Var( "x", i )
  val y = Var( "y", i )
  val z = Var( "z", i )
  val eq = Const( "=", i -> ( i -> o ) )
  val P = Const( "P", i -> ( i -> ( i -> o ) ) )
  val Q = Const( "Q", i -> o )
  val R = Const( "R", i -> o )

  val et1 = ETWeakQuantifier(
    Ex( x, HOLAtom( eq, x :: x :: Nil ) ),
    List( ( ETAtom( HOLAtom( eq, c :: c :: Nil ) ), c ) ) )

  val et2 = ETWeakQuantifier(
    Ex( x, HOLAtom( P, x :: y :: c :: Nil ) ),
    List( ( ETAtom( HOLAtom( P, z :: y :: c :: Nil ) ), z ) ) )

  val et3 = ETStrongQuantifier(
    All( x, HOLAtom( P, x :: d :: z :: Nil ) ),
    z,
    ETAtom( HOLAtom( P, z :: d :: z :: Nil ) ) )

  val et4 = ETWeakQuantifier(
    Ex( x, HOLAtom( P, x :: c :: a :: Nil ) ),
    List(
      ( ETAtom( HOLAtom( P, z :: c :: a :: Nil ) ), z ),
      ( ETAtom( HOLAtom( P, y :: c :: a :: Nil ) ), y ) ) )

  val et5 = ETImp(
    ETWeakQuantifier(
      All( x, HOLAtom( R, x :: Nil ) ),
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
        Ex( x, HOLAtom( P, x :: d :: c :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, z :: d :: c :: Nil ) ), z ) ) )
    }

    "replace variables correctly 2" in {
      val s = HOLSubstitution( z, d )
      val etPrime = substitute( s, et2 )

      etPrime mustEqual ETWeakQuantifier(
        Ex( x, HOLAtom( P, x :: y :: c :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, d :: y :: c :: Nil ) ), d ) ) )
    }

    "replace variables correctly 3" in {
      val s = HOLSubstitution( z, y )
      val etPrime = substitute( s, et3 )

      etPrime mustEqual ETStrongQuantifier(
        All( x, HOLAtom( P, x :: d :: y :: Nil ) ),
        y,
        ETAtom( HOLAtom( P, y :: d :: y :: Nil ) ) )
    }

    "not replace const " in {
      val s = HOLSubstitution( Var( "c", i ), Const( "d", i ) )
      val etPrime = substitute( s, et1 )

      etPrime mustEqual et1
    }

    "create merge node in case of collapse in weak quantifier instances " in {
      val s = HOLSubstitution( z, y )
      val etPrime = substitute.applyNoMerge( s, et4 )

      etPrime mustEqual ETWeakQuantifier(
        Ex( x, HOLAtom( P, x :: c :: a :: Nil ) ),
        List(
          ( ETMerge( ETAtom( HOLAtom( P, y :: c :: a :: Nil ) ), ETAtom( HOLAtom( P, y :: c :: a :: Nil ) ) ), y ) ) )
    }
  }

  "Expansion Trees merge" should {
    "merge identical trees" in {
      merge( ETMerge( et4, et4 ) ) mustEqual et4
    }

    "do simple substitution as result of merge" in {
      val etSubst1 = ETNeg( ETStrongQuantifier( All( x, HOLAtom( Q, x :: Nil ) ), z, ETAtom( HOLAtom( Q, z :: Nil ) ) ) )
      val etSubst2 = ETNeg( ETStrongQuantifier( All( x, HOLAtom( Q, x :: Nil ) ), y, ETAtom( HOLAtom( Q, y :: Nil ) ) ) )

      // from a theoretical point of view, the result could also be equal to the second tree, but users probably expect the algo to work from left to right
      merge( ETMerge( etSubst1, etSubst2 ) ) mustEqual etSubst1
    }

    "do simple substitution as result of merge with context" in {
      val etSubst1 = ETNeg( ETStrongQuantifier( All( x, HOLAtom( Q, x :: Nil ) ), z, ETAtom( HOLAtom( Q, z :: Nil ) ) ) )
      val etSubst2 = ETNeg( ETStrongQuantifier( All( x, HOLAtom( Q, x :: Nil ) ), y, ETAtom( HOLAtom( Q, y :: Nil ) ) ) )
      merge( ETMerge( etSubst1, etSubst2 ) ) mustEqual etSubst1
    }

    "do merge with substitution in other tree of sequent triggered by merge" in {
      // example from Chaudhuri et.al : A multi-focused proof system isomorphic to expansion proofs
      val etSubst1 = ETStrongQuantifier( All( x, HOLAtom( R, x :: Nil ) ), z, ETAtom( HOLAtom( R, z :: Nil ) ) )
      val etSubst2 = ETStrongQuantifier( All( x, HOLAtom( R, x :: Nil ) ), y, ETAtom( HOLAtom( R, y :: Nil ) ) )
      val fy = HOLFunction( f, y :: Nil )
      val fz = HOLFunction( f, z :: Nil )
      val seq = ( Nil,
        // only succedent:
        ETMerge( etSubst1, etSubst2 ) ::
        ETWeakQuantifier( Ex( x, HOLAtom( R, x :: Nil ) ), List(
          ( ETAtom( HOLAtom( R, fz :: Nil ) ), fz ),
          ( ETAtom( HOLAtom( R, fy :: Nil ) ), fy ) ) ) ::
        ETAtom( HOLAtom( R, z :: Nil ) ) ::
        ETAtom( HOLAtom( R, y :: Nil ) ) ::
        Nil )
      val mergedSeq = merge( seq )

      // merge will trigger a substitution y -> z

      val testResult = new ExpansionSequent( Nil,
        ( ETStrongQuantifier( All( x, HOLAtom( R, x :: Nil ) ), z, ETAtom( HOLAtom( R, z :: Nil ) ) ) ::
          ETWeakQuantifier( Ex( x, HOLAtom( R, x :: Nil ) ), List( ( ETAtom( HOLAtom( R, fz :: Nil ) ), fz ) ) ) ::
          ETAtom( HOLAtom( R, z :: Nil ) ) ::
          ETAtom( HOLAtom( R, z :: Nil ) ) ::
          Nil ).asInstanceOf[Seq[ExpansionTree]] )

      mergedSeq mustEqual testResult
    }

  }

  "toDeep" should {
    "correctly compute the deep formula" in {
      val form = Imp(
        And(
          HOLAtom( R, c :: Nil ),
          HOLAtom( R, d :: Nil ) ),
        And(
          HOLAtom( R, c :: Nil ),
          HOLAtom( R, d :: Nil ) ) )

      val deep = toDeep( et5, 1 )

      deep mustEqual form
    }
  }

}

