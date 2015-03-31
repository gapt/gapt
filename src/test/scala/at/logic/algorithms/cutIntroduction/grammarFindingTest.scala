package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle.parseTerm
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }
import at.logic.provers.minisat.MiniSAT
import at.logic.provers.sat4j.Sat4j
import org.specs2.mutable._

class GrammarFindingTest extends Specification {
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  "normalForms" should {
    "find strong normal forms" in {
      val nfs = normalForms( Seq( "f(c)", "f(d)" ) map parseTerm, Seq( x ) )
      nfs.toSet must beEqualTo( Set( "f(c)", "f(d)", "f(x)", "x" ) map parseTerm )
    }
    "not introduce equations between non-terminals" in {
      val nfs = normalForms( Seq( "f(c,c)", "f(d,d)" ) map parseTerm, Seq( x ) )
      nfs.toSet must beEqualTo( Set( "f(x,x)", "f(c,c)", "f(d,d)", "x" ) map parseTerm )
    }
  }
  "tratNormalForms" should {
    "find strong normal forms" in {
      val nfs = tratNormalForms( Seq( "f(c)", "f(d)" ) map parseTerm, Seq( x ) )
      nfs.toSet must beEqualTo( Set( "c", "d", "f(c)", "f(d)", "f(x)", "x" ) map parseTerm )
    }
    "not introduce equations between non-terminals" in {
      val nfs = tratNormalForms( Seq( "f(c,c)", "f(d,d)" ) map parseTerm, Seq( x ) )
      nfs.toSet must beEqualTo( Set( "f(x,x)", "f(c,c)", "f(d,d)", "x", "c", "d" ) map parseTerm )
    }
  }

  "VectGrammarMinimizationFormula" should {
    def vtg( nts: Seq[String], prods: Seq[String]* ) =
      VectTratGrammar( FOLVar( "x" ), nts map { nt => nt.split( "," ).map( FOLVar( _ ) ).toList },
        prods map { vect =>
          vect.map( p => FOLVar( p.split( "->" )( 0 ) ) ).toList -> vect.map( p => parseTerm( p.split( "->" )( 1 ) ) ).toList
        } toList )

    def covers( g: VectTratGrammar, terms: String* ) = terms foreach { term =>
      new Sat4j().solve( new VectGrammarMinimizationFormula( g ).generatesTerm( parseTerm( term ) ) ) aka s"$g covers $term" must beSome
    }

    def doesNotCover( g: VectTratGrammar, terms: String* ) =
      terms foreach { term =>
        new Sat4j().solve( new VectGrammarMinimizationFormula( g ).generatesTerm( parseTerm( term ) ) ) aka s"$g does NOT generate $term" must beNone
      }

    "simple" in {
      val g = vtg( Seq( "x", "y1,y2" ),
        Seq( "x->r(y1,y2)" ), Seq( "y1->c", "y2->d" ), Seq( "y1->d", "y2->c" ) )
      covers( g, "r(c,d)", "r(d,c)" )
      doesNotCover( g, "r(c,c)", "r(d,d)" )
      ok
    }

    "undefined values" in {
      val g = vtg( Seq( "x", "y1,y2,y3" ),
        Seq( "x->r(y1,y2)" ), Seq( "y1->c", "y2->d", "y3->d" ), Seq( "y1->d", "y2->c", "y3->e" ) )
      covers( g, "r(c,d)", "r(d,c)" )
      doesNotCover( g, "r(c,c)", "r(d,d)" )
      ok
    }

    "not require unnecessary productions" in {
      val g = vtg( Seq( "x", "y", "z" ),
        Seq( "x->r(y)" ), Seq( "x->r(z)" ), Seq( "y->c" ), Seq( "z->d" ) )
      val p = g.productions( 3 ) // z->d

      val f = new VectGrammarMinimizationFormula( g )
      new Sat4j().solve( And( f.generatesTerm( parseTerm( "r(c)" ) ), Neg( f.vectProductionIsIncluded( p ) ) ) ) must beSome
    }
  }

  "GrammarMinimizationFormula" should {
    "generate term with 2 productions" in {
      val g = TratGrammar( x, Seq( x -> parseTerm( "f(y)" ), y -> parseTerm( "c" ) ) )
      val formula = GrammarMinimizationFormula( g, parseTerm( "f(c)" ) )
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
      new Sat4j().solve( GrammarMinimizationFormula( g, parseTerm( "c" ) ) ) must beSome
      new Sat4j().solve( GrammarMinimizationFormula( g, parseTerm( "d" ) ) ) must beNone
      ok
    }
  }

  "minimizeGrammar" should {
    "remove redundant productions" in {
      if ( !new MaxSAT( MaxSATSolver.ToySolver ).isInstalled ) skipped( "toysolver not installed" )

      val g = TratGrammar( x, Seq( x -> parseTerm( "c" ), x -> parseTerm( "d" ) ) )
      val minG = minimizeGrammar( g, Seq( parseTerm( "c" ) ) )
      minG.productions must beEqualTo( Seq( x -> parseTerm( "c" ) ) )
    }
  }

  "findMinimalGrammar" should {
    "find covering grammar" in {
      if ( !new MaxSAT( MaxSATSolver.ToySolver ).isInstalled ) skipped( "toysolver not installed" )

      val l = Seq( "g(c,c)", "g(d,d)", "g(e,e)", "f(c,c)", "f(d,d)", "f(e,e)" ) map parseTerm
      val g = findMinimalGrammar( l, 1 )
      new Sat4j().solve( GrammarMinimizationFormula( g, l ) ) must beSome
      g.productions.size must beEqualTo( 2 + 3 )
    }
  }
}
