package gapt.formats.lisp

import org.specs2.mutable._
import scala.util.{Success, Failure}

class SExpressionTest extends Specification {

  "keywords should print correctly" in {
    LKeyword("keyword").toString must_== ":keyword"
  }

  "symbols without special characters should be unquoted" in {
    LSymbol("symbol").toString must_== "symbol"
  }

  "symbols" in {
    "symbols beginning with ':' should be quoted" in {
      LSymbol(":symbol").toString must_== "|:symbol|"
    }

    "empty symbol should print as ||" in {
      LSymbol("").toString must_== "||"
    }

    "symbols containing special characters should be quoted" in {
      LSymbol("\n").toString must_== "|\n|"
      LSymbol("\r").toString must_== "|\r|"
      LSymbol("\t").toString must_== "|\t|"
      LSymbol("\f").toString must_== "|\f|"
      LSymbol(" ").toString must_== "| |"
      LSymbol("\"").toString must_== "|\"|"
      LSymbol("(").toString must_== "|(|"
      LSymbol(")").toString must_== "|)|"
      LSymbol(";").toString must_== "|;|"
    }
    "the characters | and \\ should be escaped" in {
      LSymbol("|").toString must_== "|\\||"
      LSymbol("\\").toString must_== "|\\\\|"
    }
  }

}
