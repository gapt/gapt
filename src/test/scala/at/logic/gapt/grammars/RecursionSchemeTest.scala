package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class RecursionSchemeTest extends Specification with SatMatchers {

  def covers( rs: RecursionScheme, ts: LambdaExpression* ) =
    ( new RecSchemGenLangFormula( rs ) )( ts map { rs.axiom -> _ } ) aka s"$rs generates $ts" must beSat

  def doesNotCover( rs: RecursionScheme, t: LambdaExpression ) =
    ( new RecSchemGenLangFormula( rs ) )( Set( rs.axiom -> t ) ) aka s"$rs generates $t" must beUnsat

  "RecSchemGenLangFormula" should {
    "first-order" in {
      val Seq( x, y, y1, y2, y3, z ) = Seq( "x", "y", "y1", "y2", "y3", "z" ) map { FOLVar( _ ) }
      val Seq( c, d, e ) = Seq( "c", "d", "e" ) map { FOLConst( _ ) }
      val q = FOLFunctionHead( "q", 1 )
      val r = FOLFunctionHead( "r", 2 )
      val f = FOLFunctionHead( "f", 2 )
      val h = FOLFunctionHead( "h", 1 )

      val A = FOLConst( "A" )

      "work for non-terminals with higher arity" in {
        val B = FOLFunctionHead( "B", 2 )
        val rs = RecursionScheme(
          A,
          A -> B( c, d ),
          A -> B( d, c ),
          B( y1, y2 ) -> r( y1, y2 )
        )
        covers( rs, r( c, d ), r( d, c ) )
        doesNotCover( rs, r( c, c ) )
        doesNotCover( rs, r( d, d ) )
      }
      "undefined values" in {
        val B = FOLFunctionHead( "B", 3 )
        val rs = RecursionScheme(
          A,
          A -> B( c, d, d ), A -> B( d, c, e ),
          B( y1, y2, y3 ) -> r( y1, y2 )
        )
        covers( rs, r( c, d ), r( d, c ) )
        doesNotCover( rs, r( c, c ) )
        doesNotCover( rs, r( d, d ) )
      }
      "not require unnecessary rules" in {
        val B = FOLFunctionHead( "B", 1 )
        val C = FOLFunctionHead( "C", 1 )
        val rs = RecursionScheme(
          A,
          A -> B( c ), A -> C( d ),
          B( x ) -> q( x ),
          C( x ) -> q( x )
        )

        val f = new RecSchemGenLangFormula( rs )
        ( f( Set( A -> q( c ) ) ) & -f.ruleIncluded( Rule( A, C( d ) ) ) ) must beSat
      }
      "generate term with 2 rules" in {
        val B = FOLFunctionHead( "B", 1 )
        val rs = RecursionScheme( A, A -> B( c ), B( x ) -> h( x ) )
        covers( rs, h( c ) )
      }
      "not generate term if rule is not included" in {
        val rs = RecursionScheme( A, A -> c )
        val formula = new RecSchemGenLangFormula( rs )
        ( formula( Set( A -> c ) ) & -formula.ruleIncluded( rs.rules.head ) ) must beUnsat
      }
      "do not derive terms from non-axioms" in {
        val B = FOLFunctionHead( "B", 0 )
        val rs = RecursionScheme( A, A -> c, B -> d )
        covers( rs, c )
        doesNotCover( rs, d )
      }
      "non-terminals without rules" in {
        val B = FOLFunctionHead( "B", 2 )
        val rs = RecursionScheme( A, Set( A, B ), A -> c )
        covers( rs, c )
      }
      "unused non-terminals" in {
        val B = FOLFunctionHead( "B", 2 )
        val rs = RecursionScheme(
          A,
          B( y1, y2 ) -> f( y1, y2 ),
          B( y1, y2 ) -> f( y2, y1 ),
          B( y1, y2 ) -> f( c, y2 )
        )
        doesNotCover( rs, f( c, d ) )
      }
    }

  }

}
