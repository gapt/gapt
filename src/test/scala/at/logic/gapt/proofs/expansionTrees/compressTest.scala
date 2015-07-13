package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansionTrees._
import org.specs2.mutable._

class compressTest extends Specification {

  val x = Var( ( "x" ), Ti )
  val c = Const( ( "c" ), Ti )
  val d = Const( ( "d" ), Ti )
  val P = Const( "P", Ti -> To )

  val et1: ExpansionTree = merge(
    ETWeakQuantifier(
      All( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, d :: Nil ) ), d ), ( ETAtom( HOLAtom( P, c :: Nil ) ), c ) )
    )
  )

  val et2: ExpansionTree = merge(
    ETWeakQuantifier(
      Ex( x, HOLAtom( P, x :: Nil ) ),
      List( ( ETAtom( HOLAtom( P, d :: Nil ) ), d ), ( ETAtom( HOLAtom( P, c :: Nil ) ), c ) )
    )
  )

  val eSeq = ExpansionSequent( List( et1 ), List( et2 ) )

  val meSeq = compressQuantifiers( eSeq )
  val eSeq2 = decompressQuantifiers( meSeq )

  // FIXME: assumes that decompressQuantifiers generates the instances in a specific order

  "Expansion tree compression and decompression" should {
    "be computed correctly" in {
      eSeq2 mustEqual eSeq
    }
  }
}
