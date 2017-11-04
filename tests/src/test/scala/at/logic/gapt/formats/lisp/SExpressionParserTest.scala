package at.logic.gapt.formats.lisp

import org.specs2.mutable._
import scala.util.{ Success, Failure }

class SExpressionParserTest extends Specification {

  "quoted symbols" in {
    "should be recognized properly" in {
      new SExpressionParser( "||" ).SExpr.run() must_== Success( LAtom( "" ) )
      new SExpressionParser( "|a\nb\nc|" ).SExpr.run() must_== Success( LAtom( "a\nb\nc" ) )
    }
    "should handle escape sequences" in {
      new SExpressionParser( "|\\\\|" ).SExpr.run() must_== Success( LAtom( "\\" ) )
      new SExpressionParser( "|\\||" ).SExpr.run() must_== Success( LAtom( "|" ) )
    }
    "with unescaped \\ should fail" in {
      new SExpressionParser( "|\\|" ).SExpr.run() match {
        case Failure( _ ) => success
        case x            => println( x ); failure
      }
    }
    "unescaped | should not be part of matched atom" in {
      new SExpressionParser( "|||" ).SExpr.run() must_== Success( LAtom( "" ) )

    }
  }
}
