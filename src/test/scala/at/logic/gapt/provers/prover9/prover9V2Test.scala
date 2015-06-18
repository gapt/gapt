package at.logic.gapt.provers.prover9

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula

import org.specs2.mutable._

class Prover9V2Test extends Specification {
  val prover9 = new Prover9ProverV2

  args( skipAll = !prover9.isInstalled )
  "The Prover9 interface" should {
    "prove identity" in {
      val k = FOLConst( "k" )
      val s = FSequent( Seq(), Seq( Eq( k, k ) ) )
      prover9.getLKProof( s ) must beSome
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val Seq( a, b ) = Seq( "A", "B" ).map( FOLAtom( _ ) )
      val s = FSequent( Seq( Or( a, b ) ), Seq( Neg( And( Neg( a ), Neg( b ) ) ) ) )
      prover9.getLKProof( s ) must beSome
    }

    "handle quantified antecedents" in {
      val seq = FSequent( Seq( "0+x=x", "s(x)+y=s(x+y)" ).map( s => univclosure( parseFormula( s ) ) ),
        Seq( parseFormula( "s(0)+s(s(0)) = s(s(s(0)))" ) ) )
      prover9.getLKProof( seq ) must beSome
    }

    "prove top" in { prover9.getLKProof( FSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { prover9.getLKProof( FSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { prover9.getLKProof( FSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { prover9.getLKProof( FSequent( Seq( Bottom() ), Seq() ) ) must beSome }
  }

}
