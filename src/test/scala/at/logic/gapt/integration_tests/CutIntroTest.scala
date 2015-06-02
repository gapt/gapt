package at.logic.gapt.integration_tests

import at.logic.gapt.language.fol.Utils
import at.logic.gapt.proofs.lk.algorithms.cutIntroduction._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr._
import at.logic.gapt.expr._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.provers.basicProver.BasicProver
import org.specs2.mutable._
import scala.collection.immutable.HashSet

class CutIntroTest extends Specification {
  private def LinearExampleTermset( n: Int ): List[FOLTerm] =
    if ( n == 0 )
      List[FOLTerm]()
    else
      Utils.numeral( n - 1 ) :: LinearExampleTermset( n - 1 )

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  private def LinearExampleProof( k: Int, n: Int ): LKProof = {
    val s = "s"
    val c = "0"
    val p = "P"

    val x = FOLVar( "x" )
    val ass = All( x, Imp( FOLAtom( p, x :: Nil ), FOLAtom( p, FOLFunction( s, x :: Nil ) :: Nil ) ) )
    if ( k == n ) // leaf proof
    {
      val a = FOLAtom( p, Utils.numeral( n ) :: Nil )
      WeakeningLeftRule( Axiom( a :: Nil, a :: Nil ), ass )
    } else {
      val p1 = FOLAtom( p, Utils.numeral( k ) :: Nil )
      val p2 = FOLAtom( p, Utils.numeral( k + 1 ) :: Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1 :: Nil, p1 :: Nil ), LinearExampleProof( k + 1, n ), p1, p2 ), aux, ass, Utils.numeral( k ) ), ass )
    }
  }

  "CutIntroduction" should {
    "extract and decompose the termset of the linear example proof (n = 4)" in {
      val proof = LinearExampleProof( 0, 4 )

      val termset = TermsExtraction( proof )
      val set = termset.set.foldRight( List[FOLTerm]() )( ( t, acc ) => termset.getTermTuple( t ) ++ acc )

      CutIntroduction.one_cut_one_quantifier( proof, false )

      set must contain( exactly( LinearExampleTermset( 4 ): _* ) )
    }

    "introduce two cuts into linear example proof (n = 8)" in {
      def fun( n: Int, t: FOLTerm ): FOLTerm = if ( n == 0 ) t else FOLFunction( "s", fun( n - 1, t ) :: Nil )
      val proof = LinearExampleProof( 0, 8 )
      val f = proof.root.antecedent.tail.head.formula.asInstanceOf[FOLFormula]
      val a1 = FOLVar( "α_1" )
      val a2 = FOLVar( "α_2" )
      val zero = FOLConst( "0" )

      val u1 = a1
      val u2 = fun( 1, a1 )
      val us = ( ( f, ( u1 :: Nil ) :: ( u2 :: Nil ) :: Nil ) :: Nil ).toMap
      val s11 = a2
      val s12 = fun( 2, a2 )
      val s21 = zero
      val s22 = fun( 4, zero )

      val ss = ( a1 :: Nil, ( s11 :: Nil ) :: ( s12 :: Nil ) :: Nil ) :: ( a2 :: Nil, ( s21 :: Nil ) :: ( s22 :: Nil ) :: Nil ) :: Nil
      val grammar = new MultiGrammar( us, ss )
      val endSequent = proof.root.toFSequent
      val ehs = new ExtendedHerbrandSequent( endSequent, grammar )
      val prover = new BasicProver()
      val result_new = MinimizeSolution( ehs, prover )
      val r_proof = CutIntroduction.buildProofWithCut( result_new, prover )

      // expected result
      val cf1 = All( a1, Or( FOLAtom( "P", fun( 2, a1 ) :: Nil ), Neg( FOLAtom( "P", a1 :: Nil ) ) ) )
      val cf2 = All( a2, Or( FOLAtom( "P", fun( 4, a2 ) :: Nil ), Neg( FOLAtom( "P", a2 :: Nil ) ) ) )

      result_new.cutFormulas must beEqualTo( cf1 :: cf2 :: Nil )

      at.logic.gapt.proofs.lk.algorithms.quantRulesNumber( r_proof.get ) must beEqualTo( grammar.size + ss.size )
    }
  }
}

