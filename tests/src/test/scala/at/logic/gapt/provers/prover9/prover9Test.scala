package at.logic.gapt.provers.prover9

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution.Input
import org.specs2.mutable._

class Prover9Test extends Specification with SequentMatchers {
  args( skipAll = !Prover9.isInstalled )
  "The Prover9 interface" should {
    "prove identity" in {
      val s = Sequent() :+ hof"k=k"
      Prover9.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( s )
      }
    }

    "prove { A or B :- -(-A and -B)  }" in {
      val s = hof"A | B" +: Sequent() :+ hof"-(-A & -B)"
      Prover9.getLKProof( s ) must beLike {
        case Some( p ) => p.endSequent must_== s
      }
    }

    "handle quantified antecedents" in {
      val seq = hof"!x 0+x=x" +: hof"!x!y s(x)+y=s(x+y)" +: Sequent() :+ hof"s(0)+s(s(0)) = s(s(s(0)))"
      Prover9.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "prove top" in { Prover9.getLKProof( HOLSequent( Seq(), Seq( Top() ) ) ) must beSome }
    "not prove bottom" in { Prover9.getLKProof( HOLSequent( Seq(), Seq( Bottom() ) ) ) must beNone }
    "not refute top" in { Prover9.getLKProof( HOLSequent( Seq( Top() ), Seq() ) ) must beNone }
    "refute bottom" in { Prover9.getLKProof( HOLSequent( Seq( Bottom() ), Seq() ) ) must beSome }

    "ground sequents" in {
      val seq = hof"x=y" +: Sequent() :+ hof"y=x"
      Prover9.getLKProof( seq ) must beLike {
        case Some( p ) => p.endSequent must beMultiSetEqual( seq )
      }
    }

    "treat variables in sequents as constants" in {
      val seq = hof"P(x)" +: Sequent() :+ hof"P(c)"
      Prover9.getExpansionProof( seq ) must beNone
    }

    "handle exit code 2" in {
      val cnf = Set( Clause(), hoa"a" +: Clause() )
      Prover9.getResolutionProof( cnf ) must beLike {
        case Some( p ) => cnf must contain( atLeast( p.subProofs.collect { case Input( seq ) => seq.asInstanceOf[HOLClause] } ) )
      }
    }
  }

  "Prover9 proof output loader" should {
    def load( fn: String ) = ClasspathInputFile( fn )

    "goat puzzle PUZ047+1.out" in {
      Prover9Importer.lkProof( load( "PUZ047+1.out" ) )
      ok
    }

    "expansion proof paper example cade13example.out" in {
      Prover9Importer.lkProof( load( "cade13example.out" ) )
      ok
    }

    "proof with new_symbol" in {
      Prover9Importer.lkProof( load( "ALG138+1.out" ) )
      ok
    }

    "other proof with new_symbol" in {
      Prover9Importer.expansionProof( load( "SEU034+1.out" ) )
      ok
    }

    "strong quantifiers" in {
      Prover9Importer.lkProof( load( "GEO200+1.out" ) )
      ok
    }

    "cnf with different equation order" in {
      Prover9Importer.lkProof( load( "NUM561+2.out" ) )
      ok
    }
  }

}
