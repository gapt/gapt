package at.logic.gapt.grammars.induction2

import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ InductionGrammar, findMinimalInductionGrammar, minimizeInductionGrammar, stableInductionGrammar }
import at.logic.gapt.grammars.InductionGrammar.Production
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
      hov"τ: o", hov"α: nat",
      Map( hoc"0" -> List(), hoc"s" -> List( hov"ν: nat" ) ),
      List(),
      Vector(
        Production( hov"τ:o", hof"p 0" ),
        Production( hov"τ:o", hof"p ν -> p (s ν)" ),
        Production( hov"τ:o", hof"-p α" ) ) )
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
      hov"τ: o", hov"α: nat",
      Map( hoc"0" -> List(), hoc"s" -> List( hov"ν: nat" ) ),
      List( hov"γ: w" ),
      Vector(
        Production( hov"τ:o", hof"p γ 0" ),
        Production( hov"τ:o", hof"p (f γ) ν -> p (g γ) ν -> p γ (s ν)" ),
        Production( hov"γ:w", le"f γ" ),
        Production( hov"γ:w", le"g γ" ),
        Production( hov"γ:w", le"c" ),
        Production( hov"τ:o", hof"-p c α" ) ) )
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
      hov"τ: o", hov"α: list",
      Map( hoc"nil" -> List(), hoc"cons" -> List( hov"ν1: i", hov"ν2: list" ) ),
      List( hov"γ: w" ),
      Vector(
        Production( hov"τ:o", hof"p γ nil" ),
        Production( hov"τ:o", hof"p (f γ) ν2 -> p (g γ) ν2 -> p γ (cons ν1 ν2)" ),
        Production( hov"γ:w", le"f γ" ),
        Production( hov"γ:w", le"g γ" ),
        Production( hov"γ:w", le"c" ),
        Production( hov"τ:o", hof"-p c α" ) ) )
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
      tau = hov"τ: o", alpha = hov"α: nat",
      nus = Map( hoc"0" -> List(), hoc"s" -> List( hov"ν: nat" ) ),
      gamma = List( hov"γ: nat" ) )
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
    val Some( minimal ) = findMinimalInductionGrammar( indexedTermset, List( hov"γ: nat" ) )
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
    val Some( minimal ) = findMinimalInductionGrammar( indexedTermset, List( hov"γ: i" ) )
    minimal.size must_== 1
  }

}
