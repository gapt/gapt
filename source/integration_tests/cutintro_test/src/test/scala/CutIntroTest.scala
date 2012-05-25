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

import at.logic.testing._

class CutIntroTest extends SpecificationWithJUnit {
  "CutIntroduction" should {

    "extract and decompose the termset of a simple proof (n = 4)" in {
      val proof = CutIntroExampleProof( 4 )

      val termset = termsExtraction( proof ).foldLeft( new HashSet[FOLTerm]() )( (s, l) => s ++ l )
      termset must beEqual( CutIntroExampleTermset( 4 ) )
    }

    "FOLSubstitution should work" in {
      val x = FOLVar( VariableStringSymbol("x") )
      val fx = Function( ConstantStringSymbol("f"), x::Nil )
      val c = FOLConst( ConstantStringSymbol("c") )
      val fc = Function( ConstantStringSymbol("f"), c::Nil )

      val res =  FOLSubstitution( fx, x, c )

      res must beEqual( fc )

    }
  }
}


