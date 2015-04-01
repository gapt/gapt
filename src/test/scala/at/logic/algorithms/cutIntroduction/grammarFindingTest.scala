package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle.parseTerm
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }
import at.logic.provers.sat4j.Sat4j
import org.specs2.matcher.MatchResult
import org.specs2.mutable._

class GrammarFindingTest extends Specification {
  "normalForms" should {
    "find strong normal forms" in {
      val nfs = normalForms( Seq( "f(c)", "f(d)" ) map parseTerm, Seq( FOLVar( "x" ) ) )
      nfs.toSet must beEqualTo( Set( "f(c)", "f(d)", "f(x)", "x" ) map parseTerm )
    }
    "not introduce equations between non-terminals" in {
      val nfs = normalForms( Seq( "f(c,c)", "f(d,d)" ) map parseTerm, Seq( FOLVar( "x" ) ) )
      nfs.toSet must beEqualTo( Set( "f(x,x)", "f(c,c)", "f(d,d)", "x" ) map parseTerm )
    }
    "not fall prey to replacements bug" in {
      val l = Seq( "tuple2(0 + 0)", "tuple2(s(0) + s(0))" )
      val nfs = Set( "x", "tuple2(x)", "tuple2(x + x)", "tuple2(0 + 0)", "tuple2(s(x) + s(x))", "tuple2(s(0) + s(0))" )
      normalForms( l map parseTerm, Seq( FOLVar( "x" ) ) ).toSet must beEqualTo( nfs map parseTerm )
    }
  }
  "tratNormalForms" should {
    "find strong normal forms" in {
      val nfs = tratNormalForms( Seq( "f(c)", "f(d)" ) map parseTerm, Seq( FOLVar( "x" ) ) )
      nfs.toSet must beEqualTo( Set( "c", "d", "f(c)", "f(d)", "f(x)", "x" ) map parseTerm )
    }
    "not introduce equations between non-terminals" in {
      val nfs = tratNormalForms( Seq( "f(c,c)", "f(d,d)" ) map parseTerm, Seq( FOLVar( "x" ) ) )
      nfs.toSet must beEqualTo( Set( "f(x,x)", "f(c,c)", "f(d,d)", "x", "c", "d" ) map parseTerm )
    }
  }

  "TermGenerationFormula" should {
    "work for production vectors" in {
      val g = vtg( Seq( "x", "y1,y2" ),
        Seq( "x->r(y1,y2)" ), Seq( "y1->c", "y2->d" ), Seq( "y1->d", "y2->c" ) )
      covers( g, "r(c,d)", "r(d,c)" )
      doesNotCover( g, "r(c,c)", "r(d,d)" )
    }
    "undefined values" in {
      val g = vtg( Seq( "x", "y1,y2,y3" ),
        Seq( "x->r(y1,y2)" ), Seq( "y1->c", "y2->d", "y3->d" ), Seq( "y1->d", "y2->c", "y3->e" ) )
      covers( g, "r(c,d)", "r(d,c)" )
      doesNotCover( g, "r(c,c)", "r(d,d)" )
    }
    "not require unnecessary productions" in {
      val g = vtg( Seq( "x", "y", "z" ),
        Seq( "x->r(y)" ), Seq( "x->r(z)" ), Seq( "y->c" ), Seq( "z->d" ) )
      val p = g.productions( 3 ) // z->d
      val f = new TermGenerationFormula( g, parseTerm( "r(c)" ) )
      new Sat4j().solve( And( f.formula, Neg( f.vectProductionIsIncluded( p ) ) ) ) must beSome
    }
    "generate term with 2 productions" in {
      val g = tg( "x->f(y)", "y->c" )
      covers( g, "f(c)" )
    }
    "not generate term if production not included" in {
      val g = tg( "x->c" )
      val p = g.productions( 0 )
      val formula = new GrammarMinimizationFormula( g )
      new Sat4j().solve( And( formula.generatesTerm( parseTerm( "c" ) ),
        Neg( formula.productionIsIncluded( p ) ) ) ) must beNone
    }
    "Lang((x, {x -> c, y -> d})) = {c}" in {
      val g = tg( "x->c", "y->d" )
      covers( g, "c" )
      doesNotCover( g, "d" )
    }
  }

  "minimizeGrammar" should {
    "remove redundant productions" in {
      if ( !new MaxSAT( MaxSATSolver.ToySolver ).isInstalled ) skipped( "toysolver not installed" )

      val g = tg( "x->c", "x->d" )
      val minG = minimizeGrammar( g, Seq( "c" ) map parseTerm )
      minG.productions must beEqualTo( Seq( "x->c" ) map parseProduction )
    }
  }

  "findMinimalGrammar" should {
    "find covering grammar" in {
      if ( !new MaxSAT( MaxSATSolver.ToySolver ).isInstalled ) skipped( "toysolver not installed" )

      val l = Seq( "g(c,c)", "g(d,d)", "g(e,e)", "f(c,c)", "f(d,d)", "f(e,e)" )
      val g = findMinimalGrammar( l map parseTerm, 1 )
      covers( g, l: _* )
      g.productions.size must beEqualTo( 2 + 3 )
    }
  }

  def parseProduction( p: String ): TratGrammar.Production =
    p.split( "->" ) match {
      case Array( a, t ) => FOLVar( a ) -> parseTerm( t )
    }

  def tg( prods: String* ) = TratGrammar( FOLVar( "x" ), prods map parseProduction toList )

  def vtg( nts: Seq[String], prods: Seq[String]* ) =
    VectTratGrammar( FOLVar( "x" ), nts map { nt => nt.split( "," ).map( FOLVar( _ ) ).toList },
      prods map { vect =>
        vect.toList map parseProduction unzip
      } toList )

  def covers( g: VectTratGrammar, terms: String* ): MatchResult[Any] = {
    terms foreach { term =>
      new Sat4j().solve( new TermGenerationFormula( g, parseTerm( term ) ).formula ) aka s"$g generates $term" must beSome
    }
    ok
  }

  def doesNotCover( g: VectTratGrammar, terms: String* ): MatchResult[Any] = {
    terms foreach { term =>
      new Sat4j().solve( new TermGenerationFormula( g, parseTerm( term ) ).formula ) aka s"$g does NOT generate $term" must beNone
    }
    ok
  }

  def covers( g: TratGrammar, terms: String* ): MatchResult[Any] = covers( g toVectTratGrammar, terms: _* )
  def doesNotCover( g: TratGrammar, terms: String* ): MatchResult[Any] = doesNotCover( g toVectTratGrammar, terms: _* )

}
