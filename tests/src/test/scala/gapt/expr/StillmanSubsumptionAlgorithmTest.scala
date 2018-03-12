/*
 * StillmanSubsumptionAlgorithmTest.scala
 *
 */

package gapt.expr

import gapt.proofs.HOLSequent
import org.specs2.mutable._

class StillmanSubsumptionAlgorithmFOLTest extends Specification {
  "StillmanSubsumptionAlgorithmFOL" should {
    val P = "P"
    val Q = "Q"
    val R = "R"
    val f = "f"
    val a = FOLConst( "a" )
    val b = FOLConst( "b" )
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val z = FOLVar( "z" )
    val Px = FOLAtom( P, x :: Nil )
    val Py = FOLAtom( P, y :: Nil )
    val Pz = FOLAtom( P, z :: Nil )
    val fxy = FOLFunction( f, x :: y :: Nil )
    val Pfxy = FOLAtom( P, fxy :: Nil )
    val Pa = FOLAtom( P, a :: Nil )
    val Pb = FOLAtom( P, b :: Nil )
    val fba = FOLFunction( f, b :: a :: Nil )
    val Pfba = FOLAtom( P, fba :: Nil )
    val Pxx = FOLAtom( P, x :: x :: Nil )
    val Pxa = FOLAtom( P, x :: a :: Nil )
    val Paa = FOLAtom( P, a :: a :: Nil )
    val Pxb = FOLAtom( P, x :: b :: Nil )
    val Pab = FOLAtom( P, a :: b :: Nil )
    val Pba = FOLAtom( P, b :: a :: Nil )
    val fx = FOLFunction( f, x :: Nil )
    val fa = FOLFunction( f, a :: Nil )
    val fb = FOLFunction( f, b :: Nil )
    val Pfx = FOLAtom( P, fx :: Nil )
    val Pfa = FOLAtom( P, fa :: Nil )
    val Pfb = FOLAtom( P, fb :: Nil )
    val Qxy = FOLAtom( Q, x :: y :: Nil )
    val Qay = FOLAtom( Q, a :: y :: Nil )
    val Rx = FOLAtom( R, x :: Nil )

    "return true on the following clauses" in {
      "P(x) | P(f(x,y)) and P(a) | P(b) | P(f(b,a))" in {
        val c1 = HOLSequent( Nil, Px :: Pfxy :: Nil )
        val c2 = HOLSequent( Nil, Pa :: Pb :: Pfba :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "Nil and P(a) | P(b) | P(f(b,a))" in {
        val c1 = HOLSequent( Nil, Nil )
        val c2 = HOLSequent( Nil, Pa :: Pb :: Pfba :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x) and P(x) | P(f(x,y))" in {
        val c1 = HOLSequent( Nil, Px :: Nil )
        val c2 = HOLSequent( Nil, Px :: Pfxy :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x) and P(x)" in {
        val c1 = HOLSequent( Nil, Px :: Nil )
        val c2 = HOLSequent( Nil, Px :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x) and P(y)" in {
        val c1 = HOLSequent( Nil, Px :: Nil )
        val c2 = HOLSequent( Nil, Py :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x,x) | P(x,a) and P(a,a)" in {
        val c1 = HOLSequent( Nil, Pxx :: Pxa :: Nil )
        val c2 = HOLSequent( Nil, Paa :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x) | Q(x,y) and P(a) | Q(a,y) | R(x)" in {
        val c1 = HOLSequent( Nil, Px :: Qxy :: Nil )
        val c2 = HOLSequent( Nil, Pa :: Qay :: Rx :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
    }
    "return false on the following clauses" in {
      "P(x) | P(f(x)) and P(f(a)) | P(f(b))" in {
        val c1 = HOLSequent( Nil, Px :: Pfx :: Nil )
        val c2 = HOLSequent( Nil, Pfa :: Pfb :: Nil )
        clauseSubsumption( c1, c2 ) must beNone
      }
      "P(a,a) and P(x,x) | P(x,a)" in {
        val c1 = HOLSequent( Nil, Paa :: Nil )
        val c2 = HOLSequent( Nil, Pxx :: Pxa :: Nil )
        clauseSubsumption( c1, c2 ) must beNone
      }
      "P(x,x) | P(x,b) and P(b,a) | P(a,b)" in {
        val c1 = HOLSequent( Nil, Pxx :: Pxb :: Nil )
        val c2 = HOLSequent( Nil, Pba :: Pab :: Nil )
        clauseSubsumption( c1, c2 ) must beNone
      }
      "P(x) | -P(x) and P(a) | -P(b)" in {
        val c1 = HOLSequent( Px :: Nil, Px :: Nil )
        val c2 = HOLSequent( Pb :: Nil, Pa :: Nil )
        clauseSubsumption( c1, c2 ) must beNone
      }
      "P(x) | -P(x) and P(y) | -P(z)" in {
        val c1 = HOLSequent( Px :: Nil, Px :: Nil )
        val c2 = HOLSequent( Pz :: Nil, Py :: Nil )
        clauseSubsumption( c1, c2 ) must beNone
      }
      "P(x) and P(a) | P(y)" in {
        val c1 = HOLSequent( Nil, Px :: Nil )
        val c2 = HOLSequent( Nil, Pa :: Py :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
    }
  }
}

class StillmanSubsumptionAlgorithmHOLTest extends Specification {
  "StillmanSubsumptionAlgorithmHOL" should {
    "return true on the following clauses" in {
      val P = Const( "P", Ti ->: Ti ->: To )
      val P1 = Const( "P", Ti ->: To )
      val Q = Const( "Q", Ti ->: To )
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val z = Var( "z", Ti )
      val q = Var( "q", Ti ->: To )
      val a = Const( "a", Ti )
      val b = Const( "b", Ti )
      val f = Const( "f", Ti ->: Ti ->: Ti ->: Ti )
      val f1 = Const( "f", Ti ->: Ti )
      val f2 = Const( "f", ( Ti ->: To ) ->: Ti ->: Ti ->: Ti )
      val f2qza = HOLFunction( f2, q :: z :: a :: Nil )
      val f1b = HOLFunction( f1, b :: Nil )
      val fyza = HOLFunction( f, y :: z :: a :: Nil )
      val Pxx = Atom( P, x :: x :: Nil )
      val Pxa = Atom( P, x :: a :: Nil )
      val Paa = Atom( P, a :: a :: Nil )
      val Pfyza_fyza = Atom( P, fyza :: fyza :: Nil )
      val Qf1b = Atom( Q, f1b :: Nil )
      val Pf2qza = Atom( P, f2qza :: f2qza :: Nil )
      val Px = Atom( P1, x :: Nil )
      val Pa = Atom( P1, a :: Nil )
      val Qx = Atom( Q, x :: Nil )

      "P(x:i,x:i) | P(x:i,a:i) and P(a:i,a:i)" in {
        val c1 = HOLSequent( Nil, Pxx :: Pxa :: Nil )
        val c2 = HOLSequent( Nil, Paa :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x:i,x:i) and P(f(y:i,z:i,a:i):i,f(y:i,z:i,a:i):i)" in {
        val c1 = HOLSequent( Nil, Pxx :: Nil )
        val c2 = HOLSequent( Nil, Pfyza_fyza :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x:i,x:i) and P(f(q:(i->o),z:i,a:i):i,f(q:(i->o),z:i,a:i):i) | -Q(f(b:i):(i->i))" in {
        val c1 = HOLSequent( Nil, Pxx :: Nil )
        val c2 = HOLSequent( Qf1b :: Nil, Pf2qza :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
      "P(x:i) and P(a:i) | Q(x:i)" in {
        val c1 = HOLSequent( Nil, Px :: Nil )
        val c2 = HOLSequent( Nil, Pa :: Qx :: Nil )
        clauseSubsumption( c1, c2 ) must beSome
      }
    }
  }
}
