package at.logic.gapt.grammars.induction2

import at.logic.gapt.expr._
import at.logic.gapt.grammars.induction2.InductionGrammar.Production
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.MutableContext
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class InductionGrammarTest extends Specification with SatMatchers {

  "nat linear" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"
    val g = InductionGrammar(
      hov"xTau: o",
      hov"xAlpha: nat",
      Map( hoc"0" -> List(), hoc"s" -> List( hov"xNu: nat" ) ),
      List(),
      Vector(
        Production( hov"xTau:o", hof"p 0" ),
        Production( hov"xTau:o", hof"p xNu -> p (s xNu)" ),
        Production( hov"xTau:o", hof"-p xAlpha" ) ) )
    ctx.check( g )
    And( g.instanceLanguage( le"s (s (s 0))" ) ) must beUnsat
  }

  "nat general" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += TBase( "w" )
    ctx += hoc"p: w>nat>o"
    ctx += hoc"f: w>w"; ctx += hoc"g: w>w"; ctx += hoc"c: w"
    val g = InductionGrammar(
      hov"xTau: o", hov"xAlpha: nat",
      Map( hoc"0" -> List(), hoc"s" -> List( hov"xNu: nat" ) ),
      List( hov"xGamma: w" ),
      Vector(
        Production( hov"xTau:o", hof"p xGamma 0" ),
        Production( hov"xTau:o", hof"p (f xGamma) xNu -> p (g xGamma) xNu -> p xGamma (s xNu)" ),
        Production( hov"xGamma:w", le"f xGamma" ),
        Production( hov"xGamma:w", le"g xGamma" ),
        Production( hov"xGamma:w", le"c" ),
        Production( hov"xTau:o", hof"-p c xAlpha" ) ) )
    ctx.check( g )
    And( g.instanceLanguage( le"s (s (s 0))" ) ) must beUnsat
  }

  "lists" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti
    ctx += InductiveType( "list", hoc"nil: list", hoc"cons: i>list>list" )
    ctx += TBase( "w" )
    ctx += hoc"p: w>list>o"
    ctx += hoc"f: w>w"; ctx += hoc"g: w>w"; ctx += hoc"c: w"
    val g = InductionGrammar(
      hov"xTau: o", hov"xAlpha: list",
      Map( hoc"nil" -> List(), hoc"cons" -> List( hov"xNu1: i", hov"xNu2: list" ) ),
      List( hov"xGamma: w" ),
      Vector(
        Production( hov"xTau:o", hof"p xGamma nil" ),
        Production( hov"xTau:o", hof"p (f xGamma) xNu2 -> p (g xGamma) xNu2 -> p xGamma (cons xNu1 xNu2)" ),
        Production( hov"xGamma:w", le"f xGamma" ),
        Production( hov"xGamma:w", le"g xGamma" ),
        Production( hov"xGamma:w", le"c" ),
        Production( hov"xTau:o", hof"-p c xAlpha" ) ) )
    ctx.check( g )
    ctx += hoc"a0: i"; ctx += hoc"a1: i"
    val x = le"cons a0 (cons a1 nil)"
    And( g.instanceLanguage( x ) ) must beUnsat
  }

  "find linear" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"
    def numeral( i: Int ): Expr = if ( i > 0 ) le"s ${numeral( i - 1 )}" else le"0"
    val indexedTermset = ( 0 to 3 ).map( n => numeral( n ) -> ( 0 until n ).map( i => le"p ${numeral( i )}" ).toSet ).toMap
    val stableGrammar = stableInductionGrammar(
      indexedTermset,
      tau = hov"xTau: o", alpha = hov"xAlpha: nat",
      nus = Map( hoc"0" -> List(), hoc"s" -> List( hov"xNu: nat" ) ),
      gamma = List( hov"xGamma: nat" ) )
    for ( ( n, ts ) <- indexedTermset )
      ts diff stableGrammar.instanceLanguage( n ) must beEmpty
    val Some( minimal ) = minimizeInductionGrammar( stableGrammar, indexedTermset )
    minimal.size must_== 1
  }

  "find linear 2" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"
    def numeral( i: Int ): Expr = if ( i > 0 ) le"s ${numeral( i - 1 )}" else le"0"
    val indexedTermset = ( 0 to 3 ).map( n => numeral( n ) -> ( 0 until n ).map( i => le"p ${numeral( i )}" ).toSet ).toMap
    val Some( minimal ) = findMinimalInductionGrammar( indexedTermset, List( hov"xGamma: nat" ) )
    minimal.size must_== 1
  }

  "find list" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += Ti
    ctx += InductiveType( "list", hoc"nil: list", hoc"cons: i>list>list" )
    ctx += hoc"p: list>o"
    def list( as: List[Expr] ): Expr =
      as match { case a :: as_ => le"cons $a ${list( as_ )}" case Nil => le"nil" }
    val as = Stream.from( 0 ).map( i => Var( s"a$i", Ti ) )
    val indexedTermset = ( 0 to 3 ).map( n => list( as.take( n ).toList ) ->
      ( 1 to n ).map( i => le"p ${list( as.slice( i, n ).toList )}" ).toSet ).toMap
    val Some( minimal ) = findMinimalInductionGrammar( indexedTermset, List( hov"xGamma: i" ) )
    minimal.size must_== 1
  }

}
