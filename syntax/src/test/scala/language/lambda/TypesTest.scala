/*
 * TypesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import org.specs._
import org.specs.runner._

import Types._

class TypesTest  extends SpecificationWithJUnit {
  "Types" should {
    "produce a binary function type ( i -> (i -> o ) )" in {
      FunctionType( To(), Ti()::Ti()::Nil ) must beEqual ( ->(Ti(), ->( Ti(), To() ) ) )
    }
    import scala.util.parsing.combinator._
    val p = new JavaTokenParsers with Types.Parsers
    "parse correctly from string (1)" in {
        ( p.parseAll(p.Type, "i").get ) must beEqual ( Ti() )
    }
    "parse correctly from string (2)" in {
        ( p.parseAll(p.Type, "o").get ) must beEqual ( To() )
    }
    "parse correctly from string (3)" in {
        ( p.parseAll(p.Type, "(i -> o)").get ) must beEqual ( ->(Ti(),To()) )
    }
    "parse correctly from string (4)" in {
        ( p.parseAll(p.Type, "((i -> o) -> o)").get ) must beEqual ( ->(->(Ti(),To()),To()) )
    }
    "parse correctly from string (5)" in {
        ( p.parseAll(p.Type, "(i -> (o -> o))").get ) must beEqual ( ->(Ti(), ->(To(),To())) )
    }
    import Types.TAImplicitConverters._
    "implicitly convert from string (1)" in {
        ( ->("(i -> (o -> o))", To()) ) must beEqual ( ->(->(Ti(), ->(To(),To())),To()) )
    }
    "extract from string (1)" in {
        ( "(i -> (o -> o))" match {
                case StringExtractor( ->(Ti(), ->(To(),To())) ) => true
                case _ => false
            } ) must beEqual ( true )
    }
  }
}
