package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.mutable._

class minimalExpansionSequentTest extends Specification {

  val x = Var( "x", Ti )
  val c = Const( "c", Ti )
  val d = Const( "d", Ti )
  val P = Const( "P", Ti -> To )

  val et1: ExpansionTree =
    ETWeakQuantifier(
      All( x, HOLAtom( P, x :: Nil ) ),
      Map( c -> ETAtom( HOLAtom( P, c :: Nil ), false ), d -> ETAtom( HOLAtom( P, d :: Nil ), false ) )
    )

  val et2: ExpansionTree =
    ETWeakQuantifier(
      Ex( x, HOLAtom( P, x :: Nil ) ),
      Map( c -> ETAtom( HOLAtom( P, c :: Nil ), true ), d -> ETAtom( HOLAtom( P, d :: Nil ), true ) )
    )

  val eSeq = ExpansionSequent( List( et1 ), List( et2 ) )

  val minESeq = List(
    ExpansionSequent( List(
      ETWeakQuantifier(
        All( x, HOLAtom( P, x :: Nil ) ),
        Map( c -> ETAtom( HOLAtom( P, c :: Nil ), false ) )
      )
    ), List(
      ETWeakQuantifier(
        Ex( x, HOLAtom( P, x :: Nil ) ),
        Map( c -> ETAtom( HOLAtom( P, c :: Nil ), true ) )
      )
    ) ),
    ExpansionSequent( List( ETWeakQuantifier(
      All( x, HOLAtom( P, x :: Nil ) ),
      Map( d -> ETAtom( HOLAtom( P, d :: Nil ), false ) )
    ) ), List(
      ETWeakQuantifier(
        Ex( x, HOLAtom( P, x :: Nil ) ),
        Map( d -> ETAtom( HOLAtom( P, d :: Nil ), true ) )
      )
    ) )
  )

  "Minimal expansion trees" should {
    "be computed correctly by the smart algorithm" in {
      minESeq mustEqual minimalExpansionSequents( eSeq, Sat4j )
    }

    "handle weakening" in {
      val E = ETAtom( FOLAtom( "Q" ), false ) +: Sequent() :+ ETImp( ETWeakening( FOLAtom( "P" ), false ), ETAtom( FOLAtom( "Q" ), true ) )
      val Some( minSeq ) = minimalExpansionSequent( E, Sat4j )
      Sat4j.isValid( toDeep( minSeq ) ) must_== true
    }
  }
}
