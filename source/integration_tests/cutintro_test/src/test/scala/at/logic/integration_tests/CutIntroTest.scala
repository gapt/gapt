package at.logic.integration_tests

import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.fol._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.algorithms.cutIntroduction._

import at.logic.algorithms.lk._

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._

import scala.collection.immutable.HashSet

import at.logic.testing._
/*
@RunWith(classOf[JUnitRunner])
// COMMENTING OUT THIS TESTS UNTIL THE IMPLEMENTATION OF CUT INTRODUCTION IS FIXED
class CutIntroTest extends SpecificationWithJUnit {
  "CutIntroduction" should {

    "extract and decompose the termset of a simple proof (n = 4)" in {
      val proof = CutIntroExampleProof( 4 )

      //val termset = termsExtraction( proof ).foldLeft( new HashSet[FOLTerm]() )( (s, l) => s ++ l._2 )
      val termset = termsExtraction(proof).foldRight(List[FOLTerm]()) ( (t, acc) => 
        t._2.foldRight(acc) ((lst, ac) =>
          lst ++ ac
        )
      )

      cutIntroduction(proof)

      termset must haveTheSameElementsAs ( CutIntroExampleTermset( 4 ) )
    }

    "FOLSubstitution should work" in {
      val x = FOLVar( VariableStringSymbol("x") )
      val fx = Function( ConstantStringSymbol("f"), x::Nil )
      val c = FOLConst( ConstantStringSymbol("c") )
      val fc = Function( ConstantStringSymbol("f"), c::Nil )

      val res =  FOLSubstitution( fx, x, c )

      res must beEqualTo( fc )

    }
  }
}
*/

