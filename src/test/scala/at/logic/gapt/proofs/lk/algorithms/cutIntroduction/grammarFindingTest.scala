package at.logic.gapt.proofs.lk.algorithms.cutIntroduction

import at.logic.gapt.provers.sat4j.Sat4j
import org.specs2.matcher.MatchResult
import org.specs2.mutable._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseTerm
import at.logic.gapt.language.fol._

class GrammarFindingTest extends Specification {
  "VectTratGrammar" should {
    "not accept cyclic grammars" in {
      vtg( Seq( "x" ), Seq( "x->x" ) ) must throwA[IllegalArgumentException]
      vtg( Seq( "x", "y" ), Seq( "y->x" ) ) must throwA[IllegalArgumentException]
      vtg( Seq( "x", "y1,y2" ), Seq( "y1->y2", "y2->c" ) ) must throwA[IllegalArgumentException]
    }
    "check that axiom is non-terminal" in {
      vtg( Seq( "y" ) ) must throwA[IllegalArgumentException]
    }
    "check that productions start with defined non-terminals" in {
      vtg( Seq( "x" ), Seq( "y->c" ) ) must throwA[IllegalArgumentException]
    }
  }

  "TratGrammar" should {
    "not accept cyclic grammars" in {
      vtg( Seq( "x" ), Seq( "x->x" ) ) must throwA[IllegalArgumentException]
      vtg( Seq( "x", "y" ), Seq( "y->x" ) ) must throwA[IllegalArgumentException]
    }
  }

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
      new Sat4j().solve( FOLAnd( f.formula, FOLNeg( f.vectProductionIsIncluded( p ) ) ) ) must beSome

    }
    "generate term with 2 productions" in {
      val g = tg( "x->f(y)", "y->c" )
      covers( g, "f(c)" )
    }
    "not generate term if production not included" in {
      val g = tg( "x->c" )
      val p = g.productions( 0 )
      val formula = new GrammarMinimizationFormula( g )
      new Sat4j().solve( FOLAnd( formula.generatesTerm( parseTerm( "c" ) ),
        FOLNeg( formula.productionIsIncluded( p ) ) ) ) must beNone
    }
    "Lang((x, {x -> c, y -> d})) = {c}" in {
      val g = tg( "x->c", "y->d" )
      covers( g, "c" )
      doesNotCover( g, "d" )
    }
    "generate term if only tau-productions are allowed" in {
      val l = Seq( "f(c)", "f(d)", "g(c)", "g(d)" ) map parseTerm
      val g = normalFormsTratGrammar( l, 4 )
      val formula = new GrammarMinimizationFormula( g )
      val onlyTauProd = FOLAnd( g.productions.toList.filter( _._1 != g.axiom ).map { p => FOLNeg( formula.productionIsIncluded( p ) ) } )
      new Sat4j().solve( FOLAnd( formula.generatesTerm( l( 0 ) ), onlyTauProd ) ) must beSome
    }
  }

  "minimizeGrammar" should {
    "remove redundant productions" in {
      val g = tg( "x->c", "x->d" )
      val minG = minimizeGrammar( g, Seq( "c" ) map parseTerm )
      minG.productions must beEqualTo( Seq( "x->c" ) map parseProduction )
    }
  }

  "findMinimalGrammar" should {
    "find covering grammar" in {
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
