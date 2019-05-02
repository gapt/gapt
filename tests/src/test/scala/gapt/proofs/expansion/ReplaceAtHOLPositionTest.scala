package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Atom
import gapt.expr.formula.Ex
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.logic.Polarity
import org.specs2.mutable._

class ReplaceAtHOLPositionTest extends Specification {
  "replaceAtHOLPosition" should {
    val P = Const( "P", Ti ->: Ti ->: To )
    val F = Var( "F", Ti ->: Ti ->: To )
    val x = Var( "x", Ti )
    val y = Var( "y", Ti )
    val a = Const( "a", Ti )
    val b = Const( "b", Ti )

    val Pxy = Atom( P, x, y )
    val Pay = Atom( P, a, y )
    val Fxy = Atom( F, x, y )
    val Fay = Atom( F, a, y )

    "correctly replace an argument in an atom" in {
      val xpos = Pxy.find( x ).head

      replaceAtHOLPosition( ETAtom( Pxy, Polarity.InSuccedent ), xpos, a ) should
        beEqualTo( ETAtom( Pay, Polarity.InSuccedent ) )
    }

    "correctly replace the predicate in an atom" in {
      val Ppos = Pxy.find( P ).head

      replaceAtHOLPosition( ETAtom( Pxy, Polarity.InSuccedent ), Ppos, F ) should
        beEqualTo( ETAtom( Fxy, Polarity.InSuccedent ) )
    }

    "correctly replace an argument in a negation" in {
      val negPxy = -Pxy
      val xPos = negPxy.find( x ).head

      replaceAtHOLPosition( ETNeg( ETAtom( Pxy, Polarity.InSuccedent ) ), xPos, a ) should
        beEqualTo( ETNeg( ETAtom( Pay, Polarity.InSuccedent ) ) )
    }

    "correctly replace the predicate in a negation" in {
      val negFxy = -Fxy
      val FPos = negFxy.find( F ).head

      replaceAtHOLPosition( ETNeg( ETAtom( Pxy, Polarity.InSuccedent ) ), FPos, P ) should
        beEqualTo( ETNeg( ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace an argument in a conjunction" in {
      val xPos = ( Pxy & Pxy ).find( x ).head

      replaceAtHOLPosition(
        ETAnd( ETAtom( Pxy, Polarity.InSuccedent ), ETAtom( Pxy, Polarity.InSuccedent ) ), xPos, a ) should
        beEqualTo( ETAnd( ETAtom( Pay, Polarity.InSuccedent ), ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace a predicate in a conjunction" in {
      val FPos = ( Pxy & Fxy ).find( F ).head

      replaceAtHOLPosition(
        ETAnd( ETAtom( Pxy, Polarity.InSuccedent ), ETAtom( Fxy, Polarity.InSuccedent ) ), FPos, P ) should
        beEqualTo( ETAnd( ETAtom( Pxy, Polarity.InSuccedent ), ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace an argument in a disjunction" in {
      val xPos = ( Pxy | Pxy ).find( x ).head

      replaceAtHOLPosition(
        ETOr( ETAtom( Pxy, Polarity.InSuccedent ), ETAtom( Pxy, Polarity.InSuccedent ) ), xPos, a ) should
        beEqualTo( ETOr( ETAtom( Pay, Polarity.InSuccedent ), ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace a predicate in a disjunction" in {
      val FPos = ( Pxy | Fxy ).find( F ).head

      replaceAtHOLPosition(
        ETOr( ETAtom( Pxy, Polarity.InSuccedent ), ETAtom( Fxy, Polarity.InSuccedent ) ), FPos, P ) should
        beEqualTo( ETOr( ETAtom( Pxy, Polarity.InSuccedent ), ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace an argument in an implication" in {
      val xPos = ( Pxy --> Pxy ).find( x ).head

      replaceAtHOLPosition(
        ETImp( ETAtom( Pxy, Polarity.InAntecedent ), ETAtom( Pxy, Polarity.InSuccedent ) ), xPos, a ) should
        beEqualTo( ETImp( ETAtom( Pay, Polarity.InAntecedent ), ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace a predicate in a implication" in {
      val FPos = ( Pxy --> Fxy ).find( F ).head

      replaceAtHOLPosition(
        ETImp( ETAtom( Pxy, Polarity.InAntecedent ), ETAtom( Fxy, Polarity.InSuccedent ) ), FPos, P ) should
        beEqualTo( ETImp( ETAtom( Pxy, Polarity.InAntecedent ), ETAtom( Pxy, Polarity.InSuccedent ) ) )
    }

    "correctly replace an argument in a strong quantifier node" in {
      val AllyFxy = All( y, Fxy )
      val xPos = AllyFxy.find( x ).head

      replaceAtHOLPosition(
        ETStrongQuantifier( AllyFxy, y, ETAtom( Fxy, Polarity.InSuccedent ) ), xPos, a ) should
        beEqualTo( ETStrongQuantifier( All( y, Fay ), y, ETAtom( Fay, Polarity.InSuccedent ) ) )
    }

    //    "correctly replace an argument in a Skolem quantifier node" in {
    //      val AllyFxy = All( y, Fxy )
    //      val xPos = AllyFxy.find( x ).head
    //
    //      replaceAtHOLPosition(
    // ETSkolemQuantifier( AllyFxy, y, ETAtom( Fxy, Polarity.InSuccedent ) ), xPos, a ) should
    // beEqualTo( ETSkolemQuantifier( All( y, Fay ), y, ETAtom( Fay, Polarity.InSuccedent ) ) )
    //    }

    "correctly replace an argument in a weak quantifier node " in {
      val ExyFxy = Ex( y, Fxy )
      val xPos = ExyFxy.find( x ).head
      //println( xPos )
      replaceAtHOLPosition(
        ETWeakQuantifier(
          ExyFxy,
          Map(
            a -> ETAtom( Atom( F, x, a ), Polarity.InSuccedent ),
            b -> ETAtom( Atom( F, x, b ), Polarity.InSuccedent ) ) ), xPos, b ) should beEqualTo(
          ETWeakQuantifier( Ex( y, Atom( F, b, y ) ), Map(
            a -> ETAtom( Atom( F, b, a ), Polarity.InSuccedent ),
            b -> ETAtom( Atom( F, b, b ), Polarity.InSuccedent ) ) ) )
    }
  }
}
