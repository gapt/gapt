package at.logic.gapt.formats.lisp

import org.specs2.mutable._
import scala.util.{ Success, Failure }

class SExpressionParserTest extends Specification {

  "quoted symbols" in {
    "should be recognized properly" in {
      new SExpressionParser( "||" ).SExpr.run() must_== Success( LSymbol( "" ) )
      new SExpressionParser( "|a\nb\nc|" ).SExpr.run() must_== Success( LSymbol( "a\nb\nc" ) )
    }
    "should handle escape sequences" in {
      new SExpressionParser( "|\\\\|" ).SExpr.run() must_== Success( LSymbol( "\\" ) )
      new SExpressionParser( "|\\||" ).SExpr.run() must_== Success( LSymbol( "|" ) )
    }
    "with unescaped \\ should fail" in {
      new SExpressionParser( "|\\|" ).SExpr.run() match {
        case Failure( _ ) => success
        case _            => failure
      }
    }
    "unescaped | should not be part of matched atom" in {
      new SExpressionParser( "|||" ).SExpr.run() must_== Success( LSymbol( "" ) )

    }
  }

  "keywords" in {
    "words starting with : should be keywords" in {
      new SExpressionParser( ":keyword" ).SExpr.run() must_== Success( LKeyword( "keyword" ) )
    }
    "keywords must contain at least one character" in {
      new SExpressionParser( ":" ).SExpr.run() match {
        case Failure( _ ) => success
        case _            => failure
      }
    }
    "keywords can occur in lists" in {
      new SExpressionParser( "(:atom1)" ).SExpr.run() must_== Success( LList( LKeyword( "atom1" ) ) )
    }
  }
}
