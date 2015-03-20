package at.logic.algorithms.cutIntroduction

import at.logic.language.fol.{ BottomC, And, FOLVar, Neg }
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle.parseTerm
import at.logic.provers.minisat.MiniSAT
import at.logic.provers.sat4j.Sat4j
import org.specs2.mutable._

class GrammarFindingTest extends Specification {
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  "normalForms" should {
    "find strong normal forms" in {
      val nfs = normalFormsWrtSubsets( Seq( "f(c)", "f(d)" ) map parseTerm, Seq( x ) )
      nfs.toSet must beEqualTo( Set( "c", "d", "f(c)", "f(d)", "f(x)", "x" ) map parseTerm )
    }
    "not introduce equations between non-terminals" in {
      val nfs = normalFormsWrtSubsets( Seq( "f(c,c)", "f(d,d)" ) map parseTerm, Seq( x ) )
      nfs.toSet must beEqualTo( Set( "f(x,x)", "f(c,c)", "f(d,d)", "x", "c", "d" ) map parseTerm )
    }
  }

  "GrammarMinimizationFormula" should {
    "generate term with 2 productions" in {
      val g = TratGrammar( x, Seq( x -> parseTerm( "f(y)" ), y -> parseTerm( "c" ) ) )
      val formula = GrammarMinimizationFormula( g ).generatesTerm( parseTerm( "f(c)" ) )
      new Sat4j().solve( formula ) must beSome
      ok
    }
    "not generate term if production not included" in {
      val p = x -> parseTerm( "c" )
      val g = TratGrammar( x, Seq( p ) )
      val formula = GrammarMinimizationFormula( g )
      new Sat4j().solve( And( formula.generatesTerm( parseTerm( "c" ) ), Neg( formula.productionIsIncluded( p ) ) ) ) must beNone
    }
    "Lang((x, {x -> c, y -> d})) = {c}" in {
      val g = TratGrammar( x, Seq( x -> parseTerm( "c" ), y -> parseTerm( "d" ) ) )
      new Sat4j().solve( GrammarMinimizationFormula( g ).generatesTerm( parseTerm( "c" ) ) ) must beSome
      new Sat4j().solve( GrammarMinimizationFormula( g ).generatesTerm( parseTerm( "d" ) ) ) must beNone
      ok
    }
  }

  "minimizeGrammar" should {
    "remove redundant productions" in {
      val g = TratGrammar( x, Seq( x -> parseTerm( "c" ), x -> parseTerm( "d" ) ) )
      val minG = minimizeGrammar( g, Seq( parseTerm( "c" ) ) )
      minG.productions must beEqualTo( Seq( x -> parseTerm( "c" ) ) )
    }
  }

  "findMinimalGrammar" should {
    "find covering grammar" in {
      val l = Seq( "f(c,c)", "f(d,d)" ) map parseTerm
      val g = findMinimalGrammar( l, 2 )

      new Sat4j().solve( GrammarMinimizationFormula( g ).coversLanguage( l ) ) must beSome
    }
  }
}
