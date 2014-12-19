/*
 * TypesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import scala.util.parsing.combinator._
import types._

@RunWith(classOf[JUnitRunner])
class TypesTest  extends SpecificationWithJUnit {
  "Types" should {
    "produce a binary function type ( i -> (i -> o ) )" in {
      FunctionType( To, Ti::Ti::Nil ) must beEqualTo ( ->(Ti, ->( Ti, To ) ) )
    }
    val p = new JavaTokenParsers with types.Parsers
    "parse correctly from string (1)" in {
      ( p.parseAll(p.Type, "i").get ) must beEqualTo ( Ti )
    }
    "parse correctly from string (2)" in {
      ( p.parseAll(p.Type, "o").get ) must beEqualTo ( To )
    }
    "parse correctly from string (3)" in {
      ( p.parseAll(p.Type, "(i -> o)").get ) must beEqualTo ( ->(Ti,To) )
    }
    "parse correctly from string (4)" in {
      ( p.parseAll(p.Type, "((i -> o) -> o)").get ) must beEqualTo ( ->(->(Ti,To),To) )
    }
    "parse correctly from string (5)" in {
      ( p.parseAll(p.Type, "(i -> (o -> o))").get ) must beEqualTo ( ->(Ti, ->(To,To)) )
    }
    "use correctly the constructor for strings string (1)" in {
      ( ->("(i -> (o -> o))", To) ) must beEqualTo ( ->(->(Ti, ->(To,To)),To) )
    }
    "extract from string (1)" in {
      ( "(i -> (o -> o))" match {
        case StringExtractor( ->(Ti, ->(To,To)) ) => true
        case _ => false
      } ) must beEqualTo ( true )
    }
  }

  "FunctionType" should {
    "be created/extracted correctly for" in {
      "(i -> (o -> o))" in {
        FunctionType(To, Ti::To::Nil) must beLike {case FunctionType(To, Ti::To::Nil) => ok}
      }
      "(i -> ((o -> o) -> i))" in {
        FunctionType(Ti, Ti::(->(To,To))::Nil) must beLike {case FunctionType(Ti, Ti::(->(To,To))::Nil) => ok}
      }
      "(i)" in {
        FunctionType(Ti, Nil) must beLike {case FunctionType(Ti, Nil) => ok}
      }
      "(i -> i -> i -> i -> i -> i -> i -> i -> i -> i -> i -> i -> o)" in {
        FunctionType(To, Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Nil) must beLike {case FunctionType(To, Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Ti::Nil) => ok}
      }
      "((i -> o) -> ((i -> o) -> (i -> o)))" in {
        FunctionType(->(Ti, To), (->(Ti, To))::(->(Ti, To))::Nil) must beLike {case FunctionType(To, (->(Ti, To))::(->(Ti, To))::Ti::Nil) => ok}
      }
    }
  }
}
