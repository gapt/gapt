package at.logic.gapt.proofs.expansionTrees.algorithms

import at.logic.gapt.language.hol._
import at.logic.gapt.expr.types._
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.provers.FailSafeProver
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class minimalExpansionSequentTest extends SpecificationWithJUnit {

  val x = HOLVar( "x", Ti )
  val c = HOLConst( "c", Ti )
  val d = HOLConst( "d", Ti )
  val P = HOLConst( "P", Ti -> To )

  val et1: ExpansionTree = merge(
    ETWeakQuantifier(
      HOLAllVar( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ), ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) )

  val et2: ExpansionTree = merge(
    ETWeakQuantifier(
      HOLExVar( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ), ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) )

  val eSeq = compressQuantifiers( ExpansionSequent( List( et1 ), List( et2 ) ) )

  val minESeq = List(
    ExpansionSequent( List( merge(
      ETWeakQuantifier(
        HOLAllVar( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ) ) ) ) ), List( merge(
      ETWeakQuantifier(
        HOLExVar( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ) ) ) ) ) ),
    ExpansionSequent( List( merge(
      ETWeakQuantifier(
        HOLAllVar( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) ) ), List( merge(
      ETWeakQuantifier(
        HOLExVar( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) ) ) ) ).map( compressQuantifiers.apply )

  "Minimal expansion trees" should {
    "be computed correctly by the smart algorithm" in {
      minESeq mustEqual minimalExpansionSequents( eSeq, FailSafeProver.getProver() )
    }
  }
}
