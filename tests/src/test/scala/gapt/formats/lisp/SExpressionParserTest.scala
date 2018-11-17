package gapt.formats.lisp

import gapt.formats.StringInputFile
import org.specs2.mutable._

import scala.util.{ Failure, Success }

class SExpressionParserTest extends Specification {

  "quoted symbols" in {
    "should be recognized properly" in {
      SExpressionParser.parse( StringInputFile( "||" ) ) must_== List( LSymbol( "" ) )
      SExpressionParser.parse( StringInputFile( "|a\nb\nc|" ) ) must_== List( LSymbol( "a\nb\nc" ) )
    }
    "should handle escape sequences" in {
      SExpressionParser.parse( StringInputFile( "|\\\\|" ) ) must_== List( LSymbol( "\\" ) )
      SExpressionParser.parse( StringInputFile( "|\\||" ) ) must_== List( LSymbol( "|" ) )
    }
    "with unescaped \\ should fail" in {
      SExpressionParser.parse( StringInputFile( "|\\|" ) ) must throwA[Exception]
    }
    "unescaped | should not be part of matched atom" in {
      SExpressionParser.parse( StringInputFile( "||||" ) ) must_== List( LSymbol( "" ), LSymbol( "" ) )
    }
  }

  "keywords" in {
    "words starting with : should be keywords" in {
      SExpressionParser.parse( StringInputFile( ":keyword" ) ) must_== List( LKeyword( "keyword" ) )
    }
    "keywords must contain at least one character" in {
      SExpressionParser.parse( StringInputFile( ":" ) ) must throwA[Exception]
    }
    "keywords can occur in lists" in {
      SExpressionParser.parse( StringInputFile( "(:atom1)" ) ) must_== List( LList( LKeyword( "atom1" ) ) )
    }
  }
}
