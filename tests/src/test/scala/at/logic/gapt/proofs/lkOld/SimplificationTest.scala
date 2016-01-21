
package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import org.specs2.mutable._

class SimplificationTest extends Specification {
  "Simplifications" should {
    val a = HOLAtom( Var( "a", To ) )
    val b = HOLAtom( Var( "b", To ) )
    val s1 = HOLSequent( a :: Nil, a :: Nil )
    val s2 = HOLSequent( b :: a :: b :: Nil, b :: b :: b :: a :: b :: Nil )
    val s3 = HOLSequent( a :: Nil, b :: Nil )
    val s4 = HOLSequent( b :: Nil, a :: Nil )

    val P = Const( "P", ( Ti -> Ti ) -> To )
    val Q = Const( "Q", ( Ti -> Ti ) -> To )
    val z = Var( "z", Ti -> Ti )
    val z2 = Var( "z2", Ti -> Ti )
    val b1 = Const( "b", Ti -> Ti )
    val Pz = HOLAtom( P, z :: Nil )
    val Pz2 = HOLAtom( P, z2 :: Nil )
    val Qb1 = HOLAtom( Q, b1 :: Nil )

    val f1a = And( Pz, Qb1 )
    val f1b = And( Pz2, Qb1 )

    val P1 = Const( "P", Ti -> To )
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val ai = Const( "a", Ti )
    val b2 = Const( "b", Ti )
    val f = Const( "f", Ti -> ( Ti -> Ti ) )
    val fxy = HOLFunction( f, x :: y :: Nil )
    val fba = HOLFunction( f, b2 :: ai :: Nil )

    val a1 = HOLAtom( P1, x :: Nil )
    val a2 = HOLAtom( P1, fxy :: Nil )
    val a3 = HOLAtom( P1, ai :: Nil )
    val a4 = HOLAtom( P1, b2 :: Nil )
    val a5 = HOLAtom( P1, fba :: Nil )

    val s9 = HOLSequent( Nil, a1 :: a2 :: Nil )
    val s10 = HOLSequent( f1a :: f1b :: Nil, a3 :: a4 :: a5 :: Nil )

    "correctly delete tautologous sequents" in {
      val list = s1 :: s2 :: s3 :: s4 :: s1 :: Nil
      val dlist = deleteTautologies( list )
      dlist.size must beEqualTo( 2 )
    }

    "correctly set-normalize a list of Sequents" in {
      val list = s1 :: s2 :: s2 :: s1 :: s2 :: s3 :: s1 :: s2 :: s4 :: s3 :: s2 :: s1 :: s2 :: s3 :: Nil
      val set = list.toSet
      set.size must beEqualTo( 4 )
    }

    "correctly remove subsumed sequents from a set of Sequents" in {
      val a = FOLConst( "a" )
      val x = FOLVar( "x" )
      val px = FOLFunction( "p", x :: Nil )
      val s = FOLConst( "s" )

      val f1 = FOLAtom( "<", a :: px :: Nil )
      val f2 = FOLAtom( "=", x :: s :: Nil )
      val f3 = FOLAtom( "=", a :: a :: Nil )
      val f4 = FOLAtom( "=", x :: x :: Nil )
      val f5 = FOLAtom( "=", x :: a :: Nil )

      val seq1f = HOLSequent( Nil, f1 :: Nil )
      val seq2f = HOLSequent( f2 :: Nil, f1 :: Nil )
      val seq3f = HOLSequent( Nil, f3 :: Nil )
      val seq4f = HOLSequent( Nil, f4 :: f5 :: Nil )

      "FOL" in {
        val ls = List( seq1f, seq2f, seq3f, seq4f )
        val ret = subsumedClausesRemoval( ls )
        ret.toSet must beEqualTo( Set( seq1f, seq4f ) )
      }
      "HOL" in {
        "1" in {
          val ls = List( s9, s10 )
          val ret = subsumedClausesRemovalHOL( ls )
          ret.size must beEqualTo( 1 )
        }
        "2" in {
          val ls = List( seq1f, seq2f, seq3f, seq4f )
          val ret = subsumedClausesRemovalHOL( ls )
          ret.toSet must beEqualTo( Set( seq1f, seq4f ) )
        }
      }
    }
  }
}
