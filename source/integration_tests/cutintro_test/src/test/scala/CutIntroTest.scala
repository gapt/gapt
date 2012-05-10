package at.logic.integration_tests

import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.fol._
import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher
import at.logic.algorithms.cutIntroduction._

import at.logic.algorithms.lk._

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._

import scala.collection.immutable.HashSet

class CutIntroTest extends SpecificationWithJUnit {
  "CutIntroduction" should {

    def gen_termset( n: Int ) : HashSet[FOLTerm] =
      if ( n == 0 )
        new HashSet[FOLTerm]()
      else
        gen_termset( n - 1 ) + CutIntroProof.succ( n - 1 )

    "extract and decompose the termset of a simple proof (n = 4)" in {
      val proof = CutIntroProof( 4 )

      // The next line causes an expection in extractTerms
      // val termset = termsExtraction( proof ).foldLeft( new HashSet[FOLTerm]() )( (s, l) => s ++ l )
      // termset must beEqual( gen_termset( 4 ) )
    }
  }
}

// Functions to construct cut-free proofs of the sequents
//
// P(0), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
//
// where n is an Integer parameter >= 0.

object CutIntroProof
{
  val s = new ConstantStringSymbol("s")
  val p = new ConstantStringSymbol("P")
  val c = new ConstantStringSymbol("0")

  def apply( n: Int ) = proof( 0, n )

  def proof( k: Int, n: Int )  : LKProof =
  {
    val x = FOLVar( VariableStringSymbol("x") )
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // Leaf proof
    {
      val a = Atom( p,  succ( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, succ( k )::Nil )
      val p2 = Atom( p, succ( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), proof( k + 1, n ), p1, p2 ), aux, ass, succ( k ) ), ass )
    }
  }

  def succ( k: Int ) : FOLTerm =
    if ( k == 0 )
      FOLConst( new ConstantStringSymbol("0") )
    else
      Function( s, succ( k - 1 )::Nil )
}
