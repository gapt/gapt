package at.logic.gapt.proofs.expansionTrees.algorithms

import at.logic.gapt.language.hol._
import at.logic.gapt.language.lambda.types.{ Ti => i, To => o }
import at.logic.gapt.proofs.expansionTrees._
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith( classOf[JUnitRunner] )
class compressTest extends SpecificationWithJUnit {

  val x = HOLVar( "x", i )
  val c = HOLConst( "c", i )
  val d = HOLConst( "d", i )
  val P = HOLConst( "P", i -> o )

  val et1: ExpansionTree = merge(
    ETWeakQuantifier(
      HOLAllVar( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ), ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) )

  val et2: ExpansionTree = merge(
    ETWeakQuantifier(
      HOLExVar( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, c :: Nil ) ), c ), ( ETAtom( HOLAtom( P, d :: Nil ) ), d ) ) ) )

  val eSeq = ExpansionSequent( List( et1 ), List( et2 ) )

  val meSeq = compressQuantifiers( eSeq )
  val eSeq2 = decompressQuantifiers( meSeq )

  "Expansion tree compression and decompression" should {
    "be computed correctly" in {
      eSeq2 mustEqual eSeq
    }
  }
}
