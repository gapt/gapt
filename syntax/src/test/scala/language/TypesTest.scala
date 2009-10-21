/*
 * TypesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import org.specs._
import org.specs.runner._


import Types._


class TypesTest  extends Specification with JUnit {
  "Types" should {
    import Types.Parsers._
    "parse correctly from string (1)" in {
        ( parseAll(Type, "i").get ) must beEqual ( Ti() )
    }
    "parse correctly from string (2)" in {
        ( parseAll(Type, "o").get ) must beEqual ( To() )
    }
    "parse correctly from string (3)" in {
        ( parseAll(Type, "(i -> o)").get ) must beEqual ( ->(Ti(),To()) )
    }
    "parse correctly from string (4)" in {
        ( parseAll(Type, "((i -> o) -> o)").get ) must beEqual ( ->(->(Ti(),To()),To()) )
    }
    "parse correctly from string (5)" in {
        ( parseAll(Type, "(i -> (o -> o))").get ) must beEqual ( ->(Ti(), ->(To(),To())) )
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
