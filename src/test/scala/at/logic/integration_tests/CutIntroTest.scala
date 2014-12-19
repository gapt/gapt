package at.logic.integration_tests

import at.logic.algorithms.cutIntroduction._
import at.logic.algorithms.lk._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.parsing.language.tptp.TPTPFOLExporter

import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import scala.collection.immutable.HashSet

@RunWith(classOf[JUnitRunner])
class CutIntroTest extends SpecificationWithJUnit {
  private def LinearExampleTermset( n : Int ) : List[FOLTerm] =
    if ( n == 0 )
      List[FOLTerm]()
    else
      Utils.numeral( n - 1 ) :: LinearExampleTermset( n - 1)

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  private def LinearExampleProof( k : Int, n : Int ) : LKProof = {
    val s = "s"
    val c = "0"
    val p = "P"

    val x = FOLVar( "x" )
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Utils.numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, Utils.numeral( k )::Nil )
      val p2 = Atom( p, Utils.numeral( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), LinearExampleProof( k + 1, n ), p1, p2 ), aux, ass, Utils.numeral( k ) ), ass )
    }
  }

  "CutIntroduction" should {
    "extract and decompose the termset of the linear example proof (n = 4)" in {
      val proof = LinearExampleProof( 0, 4 )

      val termset = TermsExtraction (proof)
      val set = termset.set.foldRight (List[FOLTerm]()) ( (t, acc) => termset.getTermTuple (t) ++ acc)

      CutIntroduction.one_cut_one_quantifier (proof, false)

      set must contain (exactly ( LinearExampleTermset( 4 ):_* ))
    }
  }
}

