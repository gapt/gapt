package at.logic.gapt.provers.EProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.proofs.resolution.inputClauses
import at.logic.gapt.proofs.{ SequentMatchers, HOLClause, HOLSequent, Sequent }
import at.logic.gapt.provers.eprover.EProver
import org.specs2.mutable._

class EProverTest extends Specification with SequentMatchers {
  args( skipAll = !EProver.isInstalled )
  "EProver" should {
    "prove identity" in {
      val k = FOLConst( "k" )
      val s = HOLSequent( Seq(), Seq( Eq( k, k ) ) )
      EProver.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val Seq( a, b ) = Seq( "A", "B" ).map( FOLAtom( _ ) )
      val s = HOLSequent( Seq( Or( a, b ) ), Seq( Neg( And( Neg( a ), Neg( b ) ) ) ) )
      EProver.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "handle quantified antecedents" in {
      val seq = HOLSequent(
        Seq( "0+x=x", "s(x)+y=s(x+y)" ).map( s => univclosure( parseFormula( s ) ) ),
        Seq( parseFormula( "s(0)+s(s(0)) = s(s(s(0)))" ) )
      )
      EProver.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "prove top" in { EProver.getLKProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { EProver.getLKProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { EProver.getLKProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { EProver.getLKProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome }

    "ground sequents" in {
      val seq = HOLSequent( Seq( parseFormula( "x=y" ) ), Seq( parseFormula( "y=x" ) ) )
      EProver.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "treat variables in sequents as constants" in {
      val seq = "P(x)" +: Sequent() :+ "P(c)" map parseFormula
      EProver getExpansionProof seq must beNone
    }

    "handle weird sequents" in {
      val cnf = List( HOLClause( Seq(), Seq() ), HOLClause( Seq( FOLAtom( "a" ) ), Seq() ) )
      EProver.getRobinsonProof( cnf ) must beLike {
        case Some( p ) => inputClauses( p ) must contain( atMost( cnf.toSet[HOLClause] ) )
      }
    }
  }

}
