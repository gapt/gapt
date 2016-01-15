package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import org.specs2.mutable._

/**
 * Created by sebastian on 7/15/15.
 */
class CleanStructureTest extends Specification {
  "CleanStructure" should {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val c = FOLConst( "c" )
    val d = FOLConst( "d" )
    val e = FOLConst( "e" )
    val P = FOLAtom( "P", Nil )
    val Q = FOLAtom( "Q", Nil )
    def R( x: FOLTerm, y: FOLTerm ) = FOLAtom( "R", List( x, y ) )

    "correctly reduce a weak conjunction" in {
      val et = ETAnd( ETWeakening( P ), ETWeakening( Q ) )

      CleanStructure( et ) must beEqualTo( ETWeakening( And( P, Q ) ) )
    }

    "correctly reduce a weak disjunction" in {
      val et = ETOr( ETWeakening( P ), ETWeakening( Q ) )

      CleanStructure( et ) must beEqualTo( ETWeakening( Or( P, Q ) ) )
    }

    "correctly reduce a weak implication" in {
      val et = ETImp( ETWeakening( P ), ETWeakening( Q ) )

      CleanStructure( et ) must beEqualTo( ETWeakening( Imp( P, Q ) ) )
    }

    "correctly reduce a weak quantifier" in {
      val et = merge( ETWeakQuantifier(
        univclosure( R( x, y ) ),
        List(
          ( ETWeakQuantifier( All( y, R( c, y ) ), List( ( ETWeakening( R( c, e ) ), e ) ) ), c ),
          ( ETWeakQuantifier( All( y, R( d, y ) ), List( ( ETAtom( R( d, e ) ), e ) ) ), d )
        )
      ) )

      CleanStructure( et ) must beEqualTo(
        merge( ETWeakQuantifier(
          univclosure( R( x, y ) ),
          List(
            ( ETWeakQuantifier( All( y, R( d, y ) ), List( ( ETAtom( R( d, e ) ), e ) ) ), d )
          )
        ) )
      )
    }
  }

}
