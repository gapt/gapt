package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.hol.universalClosure
import org.specs2.mutable._

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
      val et = ETAnd( ETWeakening( P, Polarity.InSuccedent ), ETWeakening( Q, Polarity.InSuccedent ) )

      cleanStructureET( et ) must beEqualTo( ETWeakening( And( P, Q ), Polarity.InSuccedent ) )
    }

    "correctly reduce a weak disjunction" in {
      val et = ETOr( ETWeakening( P, Polarity.InSuccedent ), ETWeakening( Q, Polarity.InSuccedent ) )

      cleanStructureET( et ) must beEqualTo( ETWeakening( Or( P, Q ), Polarity.InSuccedent ) )
    }

    "correctly reduce a weak implication" in {
      val et = ETImp( ETWeakening( P, Polarity.InAntecedent ), ETWeakening( Q, Polarity.InSuccedent ) )

      cleanStructureET( et ) must beEqualTo( ETWeakening( Imp( P, Q ), Polarity.InSuccedent ) )
    }

    "correctly reduce a weak quantifier" in {
      val et = ETWeakQuantifier(
        universalClosure( R( x, y ) ),
        Map(
          c -> ETWeakQuantifier( All( y, R( c, y ) ), Map( e -> ETWeakening( R( c, e ), Polarity.InAntecedent ) ) ),
          d -> ETWeakQuantifier( All( y, R( d, y ) ), Map( e -> ETAtom( R( d, e ), Polarity.InAntecedent ) ) ) ) )

      cleanStructureET( et ) must beEqualTo(
        ETWeakQuantifier(
          universalClosure( R( x, y ) ),
          Map(
            d -> ETWeakQuantifier( All( y, R( d, y ) ), Map( e -> ETAtom( R( d, e ), Polarity.InAntecedent ) ) ) ) ) )
    }
  }

}
