package at.logic.gapt.proofs.expansionTrees.algorithms

import at.logic.gapt.expr._
import at.logic.gapt.expr.types._
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.provers.FailSafeProver
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class minimalExpansionSequentTest extends SpecificationWithJUnit {

  val x = Var( "x", Ti )
  val c = Const( "c", Ti )
  val d = Const( "d", Ti )
  val P = Const( "P", Ti -> To )

  val et1: ExpansionTree = merge(
    ETWeakQuantifier(
      All( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ), ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) )

  val et2: ExpansionTree = merge(
    ETWeakQuantifier(
      Ex( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ), ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) )

  val eSeq = compressQuantifiers( ExpansionSequent( List( et1 ), List( et2 ) ) )

  val minESeq = List(
    ExpansionSequent( List( merge(
      ETWeakQuantifier(
        All( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ) ) ) ) ), List( merge(
      ETWeakQuantifier(
        Ex( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ) ) ) ) ) ),
    ExpansionSequent( List( merge(
      ETWeakQuantifier(
        All( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) ) ), List( merge(
      ETWeakQuantifier(
        Ex( x, HOLAtom( P, x :: Nil ) ),
        List( ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) ) ) ) ).map( compressQuantifiers.apply )

  "Minimal expansion trees" should {
    "be computed correctly by the smart algorithm" in {
      minESeq mustEqual minimalExpansionSequents( eSeq, FailSafeProver.getProver() )
    }
  }
}
