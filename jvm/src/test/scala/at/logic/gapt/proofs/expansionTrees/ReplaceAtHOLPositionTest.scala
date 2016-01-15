package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import org.specs2.mutable._

/**
 * Created by sebastian on 7/22/15.
 */
class ReplaceAtHOLPositionTest extends Specification {
  "replaceAtHOLPosition" should {
    val P = Const( "P", Ti -> ( Ti -> To ) )
    val F = Var( "F", Ti -> ( Ti -> To ) )
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val a = Const( "a", Ti )
    val b = Const( "b", Ti )

    val Pxy = HOLAtom( P, x, y )
    val Pay = HOLAtom( P, a, y )
    val Fxy = HOLAtom( F, x, y )
    val Fay = HOLAtom( F, a, y )

    "correctly replace an argument in an atom" in {
      val xpos = Pxy.find( x ).head

      replaceAtHOLPosition( ETAtom( Pxy ), xpos, a ) should beEqualTo( ETAtom( Pay ) )
    }

    "correctly replace the predicate in an atom" in {
      val Ppos = Pxy.find( P ).head

      replaceAtHOLPosition( ETAtom( Pxy ), Ppos, F ) should beEqualTo( ETAtom( Fxy ) )
    }

    "correctly replace an argument in a negation" in {
      val negPxy = -Pxy
      val xPos = negPxy.find( x ).head

      replaceAtHOLPosition( ETNeg( ETAtom( Pxy ) ), xPos, a ) should beEqualTo( ETNeg( ETAtom( Pay ) ) )
    }

    "correctly replace the predicate in a negation" in {
      val negFxy = -Fxy
      val FPos = negFxy.find( F ).head

      replaceAtHOLPosition( ETNeg( ETAtom( Pxy ) ), FPos, P ) should beEqualTo( ETNeg( ETAtom( Pxy ) ) )
    }

    "correctly replace an argument in a conjunction" in {
      val xPos = ( Pxy & Pxy ).find( x ).head

      replaceAtHOLPosition( ETAnd( ETAtom( Pxy ), ETAtom( Pxy ) ), xPos, a ) should beEqualTo( ETAnd( ETAtom( Pay ), ETAtom( Pxy ) ) )
    }

    "correctly replace a predicate in a conjunction" in {
      val FPos = ( Pxy & Fxy ).find( F ).head

      replaceAtHOLPosition( ETAnd( ETAtom( Pxy ), ETAtom( Fxy ) ), FPos, P ) should beEqualTo( ETAnd( ETAtom( Pxy ), ETAtom( Pxy ) ) )
    }

    "correctly replace an argument in a disjunction" in {
      val xPos = ( Pxy | Pxy ).find( x ).head

      replaceAtHOLPosition( ETOr( ETAtom( Pxy ), ETAtom( Pxy ) ), xPos, a ) should beEqualTo( ETOr( ETAtom( Pay ), ETAtom( Pxy ) ) )
    }

    "correctly replace a predicate in a disjunction" in {
      val FPos = ( Pxy | Fxy ).find( F ).head

      replaceAtHOLPosition( ETOr( ETAtom( Pxy ), ETAtom( Fxy ) ), FPos, P ) should beEqualTo( ETOr( ETAtom( Pxy ), ETAtom( Pxy ) ) )
    }

    "correctly replace an argument in an implication" in {
      val xPos = ( Pxy --> Pxy ).find( x ).head

      replaceAtHOLPosition( ETImp( ETAtom( Pxy ), ETAtom( Pxy ) ), xPos, a ) should beEqualTo( ETImp( ETAtom( Pay ), ETAtom( Pxy ) ) )
    }

    "correctly replace a predicate in a implication" in {
      val FPos = ( Pxy --> Fxy ).find( F ).head

      replaceAtHOLPosition( ETImp( ETAtom( Pxy ), ETAtom( Fxy ) ), FPos, P ) should beEqualTo( ETImp( ETAtom( Pxy ), ETAtom( Pxy ) ) )
    }

    "correctly replace an argument in a strong quantifier node" in {
      val AllyFxy = All( y, Fxy )
      val xPos = AllyFxy.find( x ).head

      replaceAtHOLPosition( ETStrongQuantifier( AllyFxy, y, ETAtom( Fxy ) ), xPos, a ) should beEqualTo( ETStrongQuantifier( All( y, Fay ), y, ETAtom( Fay ) ) )
    }

    "correctly replace an argument in a Skolem quantifier node" in {
      val AllyFxy = All( y, Fxy )
      val xPos = AllyFxy.find( x ).head

      replaceAtHOLPosition( ETSkolemQuantifier( AllyFxy, y, ETAtom( Fxy ) ), xPos, a ) should beEqualTo( ETSkolemQuantifier( All( y, Fay ), y, ETAtom( Fay ) ) )
    }

    "correctly replace an argument in a weak quantifier node " in {
      val ExyFxy = Ex( y, Fxy )
      val xPos = ExyFxy.find( x ).head
      println( xPos )
      replaceAtHOLPosition( merge( ETWeakQuantifier( ExyFxy, ( ETAtom( HOLAtom( F, x, a ) ), a ), ( ETAtom( HOLAtom( F, x, b ) ), b ) ) ), xPos, b ) should beEqualTo( merge( ETWeakQuantifier( Ex( y, HOLAtom( F, b, y ) ), ( ETAtom( HOLAtom( F, b, a ) ), a ), ( ETAtom( HOLAtom( F, b, b ) ), b ) ) ) )
    }
  }
}
