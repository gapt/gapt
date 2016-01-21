package at.logic.gapt.integration_tests

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.expr.hol.{ lcomp, containsQuantifier }
import at.logic.gapt.proofs.{ Sequent, Ant }
import at.logic.gapt.proofs.expansion.FOLInstanceTermEncoding
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.lk.{ CutRule, quantRulesNumber }
import at.logic.gapt.provers.basicProver.BasicProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.maxsat.MaxSat4j
import org.specs2.mutable._

class CutIntroTest extends Specification {
  private def LinearExampleTermset( n: Int ): List[FOLTerm] =
    if ( n == 0 )
      List[FOLTerm]()
    else
      Utils.numeral( n - 1 ) :: LinearExampleTermset( n - 1 )

  "CutIntroduction" should {
    "extract and decompose the termset of the linear example proof (n = 4)" in {
      val proof = LinearExampleProof( 4 )

      val ( termset, _ ) = FOLInstanceTermEncoding( proof )
      val set = termset collect { case FOLFunction( _, List( arg ) ) => arg }

      CutIntroduction.compressLKProof(
        proof,
        method = DeltaTableMethod( manyQuantifiers = false ),
        verbose = false
      ) must beSome

      set must contain( exactly( LinearExampleTermset( 4 ): _* ) )
    }

    "linear equality example" in {
      skipped( "actually has herbrand complexity 2... better examples welcome" )
      val f = FOLFunctionConst( "f", 1 )
      val x = FOLVar( "x" )
      val c = FOLConst( "c" )

      val Some( p ) = Escargot getLKProof ( All( x, f( x ) === x ) +: Sequent() :+ ( f( f( f( f( f( f( f( f( f( c ) ) ) ) ) ) ) ) ) === c ) )
      val Some( q ) = CutIntroduction.compressLKProof( p, MaxSATMethod( MaxSat4j, 1 ), verbose = false )
      val cutFormulas = q.subProofs collect { case c: CutRule => c.cutFormula } filter { containsQuantifier( _ ) }
      cutFormulas must contain( atMost(
        All( x, f( f( f( x ) ) ) === x ),
        All( x, x === f( f( f( x ) ) ) )
      ) )
    }

    "introduce two cuts into linear example proof with improveSolutionLK" in {
      def fun( n: Int, t: FOLTerm ): FOLTerm = if ( n == 0 ) t else FOLFunction( "s", fun( n - 1, t ) :: Nil )
      val proof = LinearExampleProof( 8 )
      val f = proof.endSequent( Ant( 0 ) ).asInstanceOf[FOLFormula]
      val a1 = FOLVar( "α_1" )
      val a2 = FOLVar( "α_2" )
      val zero = FOLConst( "0" )

      val u1 = a1
      val u2 = fun( 1, a1 )
      val us = for ( f <- proof.endSequent )
        yield f.asInstanceOf[FOLFormula] -> ( if ( containsQuantifier( f ) ) List( List( u1 ), List( u2 ) ) else List( List() ) )
      val s11 = a2
      val s12 = fun( 2, a2 )
      val s21 = zero
      val s22 = fun( 4, zero )

      val ss = ( a1 :: Nil, ( s11 :: Nil ) :: ( s12 :: Nil ) :: Nil ) :: ( a2 :: Nil, ( s21 :: Nil ) :: ( s22 :: Nil ) :: Nil ) :: Nil
      val grammar = new SchematicExtendedHerbrandSequent( us, ss )
      val ehs = ExtendedHerbrandSequent( grammar, CutIntroduction.computeCanonicalSolution( grammar ) )
      val prover = BasicProver
      val result_new = improveSolutionLK( ehs, prover, hasEquality = false )
      val r_proof = CutIntroduction.buildProofWithCut( result_new, prover )

      // expected result
      val cf1 = All( a1, FOLAtom( "P", a1 ) --> FOLAtom( "P", fun( 2, a1 ) ) )
      val cf2 = All( a2, FOLAtom( "P", a2 ) --> FOLAtom( "P", fun( 4, a2 ) ) )

      result_new.cutFormulas must beEqualTo( cf1 :: cf2 :: Nil )

      quantRulesNumber( r_proof ) must_== grammar.size
    }
  }
}

