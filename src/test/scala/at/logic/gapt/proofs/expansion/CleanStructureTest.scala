package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import org.specs2.mutable._

/**
 * Created by sebastian on 7/15/15.
 */
class CleanStructureTest extends Specification {
  "cleanStructureET" should {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val c = FOLConst( "c" )
    val d = FOLConst( "d" )
    val e = FOLConst( "e" )
    val P = FOLAtom( "P", Nil )
    val Q = FOLAtom( "Q", Nil )
    def R( x: FOLTerm, y: FOLTerm ) = FOLAtom( "R", List( x, y ) )

    "correctly reduce a weak conjunction" in {
      val et = ETAnd( ETWeakening( P, true ), ETWeakening( Q, true ) )

      cleanStructureET( et ) must beEqualTo( ETWeakening( And( P, Q ), true ) )
    }

    "correctly reduce a weak disjunction" in {
      val et = ETOr( ETWeakening( P, true ), ETWeakening( Q, true ) )

      cleanStructureET( et ) must beEqualTo( ETWeakening( Or( P, Q ), true ) )
    }

    "correctly reduce a weak implication" in {
      val et = ETImp( ETWeakening( P, false ), ETWeakening( Q, true ) )

      cleanStructureET( et ) must beEqualTo( ETWeakening( Imp( P, Q ), true ) )
    }

    "correctly reduce a weak quantifier" in {
      val et = ETWeakQuantifier(
        univclosure( R( x, y ) ),
        Map(
          c -> ETWeakQuantifier( All( y, R( c, y ) ), Map( e -> ETWeakening( R( c, e ), false ) ) ),
          d -> ETWeakQuantifier( All( y, R( d, y ) ), Map( e -> ETAtom( R( d, e ), false ) ) )
        )
      )

      cleanStructureET( et ) must beEqualTo(
        ETWeakQuantifier(
          univclosure( R( x, y ) ),
          Map(
            d -> ETWeakQuantifier( All( y, R( d, y ) ), Map( e -> ETAtom( R( d, e ), false ) ) )
          )
        )
      )
    }
  }

}
