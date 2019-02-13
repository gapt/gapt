package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.proofs.Sequent
import gapt.provers.sat.Sat4j
import org.specs2.mutable._

class minimalExpansionSequentTest extends Specification {

  val x = Var( "x", Ti )
  val c = Const( "c", Ti )
  val d = Const( "d", Ti )
  val P = Const( "P", Ti ->: To )

  val et1: ExpansionTree =
    ETWeakQuantifier(
      All( x, Atom( P, x :: Nil ) ),
      Map( c -> ETAtom( Atom( P, c :: Nil ), Polarity.InAntecedent ), d -> ETAtom( Atom( P, d :: Nil ), Polarity.InAntecedent ) ) )

  val et2: ExpansionTree =
    ETWeakQuantifier(
      Ex( x, Atom( P, x :: Nil ) ),
      Map( c -> ETAtom( Atom( P, c :: Nil ), Polarity.InSuccedent ), d -> ETAtom( Atom( P, d :: Nil ), Polarity.InSuccedent ) ) )

  val eSeq = ExpansionSequent( List( et1 ), List( et2 ) )

  val minESeq = List(
    ExpansionSequent( List(
      ETWeakQuantifier(
        All( x, Atom( P, x :: Nil ) ),
        Map( c -> ETAtom( Atom( P, c :: Nil ), Polarity.InAntecedent ) ) ) ), List(
      ETWeakQuantifier(
        Ex( x, Atom( P, x :: Nil ) ),
        Map( c -> ETAtom( Atom( P, c :: Nil ), Polarity.InSuccedent ) ) ) ) ),
    ExpansionSequent( List( ETWeakQuantifier(
      All( x, Atom( P, x :: Nil ) ),
      Map( d -> ETAtom( Atom( P, d :: Nil ), Polarity.InAntecedent ) ) ) ), List(
      ETWeakQuantifier(
        Ex( x, Atom( P, x :: Nil ) ),
        Map( d -> ETAtom( Atom( P, d :: Nil ), Polarity.InSuccedent ) ) ) ) ) )

  "Minimal expansion trees" should {
    "be computed correctly by the smart algorithm" in {
      minESeq mustEqual minimalExpansionSequents( eSeq, Sat4j )
    }

    "handle weakening" in {
      val E = ETAtom( FOLAtom( "Q" ), Polarity.InAntecedent ) +: Sequent() :+ ETImp( ETWeakening( FOLAtom( "P" ), Polarity.InAntecedent ), ETAtom( FOLAtom( "Q" ), Polarity.InSuccedent ) )
      val Some( minSeq ) = minimalExpansionSequent( E, Sat4j )
      Sat4j.isValid( minSeq.deep ) must_== true
    }
  }
}
