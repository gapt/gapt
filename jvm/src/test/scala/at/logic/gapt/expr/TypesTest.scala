/*
 * TypesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.expr

import org.specs2.mutable._
import scala.util.parsing.combinator._

class TypesTest extends Specification {
  "Types" should {
    "produce a binary function type ( i -> (i -> o ) )" in {
      FunctionType( To, Ti :: Ti :: Nil ) must beEqualTo( Ti -> ( Ti -> To ) )
    }
  }

  "FunctionType" should {
    "be created/extracted correctly for" in {
      "(i -> (o -> o))" in {
        FunctionType( To, Ti :: To :: Nil ) must beLike { case FunctionType( To, Ti :: To :: Nil ) => ok }
      }
      "(i -> ((o -> o) -> i))" in {
        FunctionType( Ti, Ti :: ( To -> To ) :: Nil ) must beLike { case FunctionType( Ti, Ti :: ( To -> To ) :: Nil ) => ok }
      }
      "(i)" in {
        FunctionType( Ti, Nil ) must beLike { case FunctionType( Ti, Nil ) => ok }
      }
      "(i -> i -> i -> i -> i -> i -> i -> i -> i -> i -> i -> i -> o)" in {
        FunctionType( To, Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Nil ) must beLike { case FunctionType( To, Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Ti :: Nil ) => ok }
      }
      "((i -> o) -> ((i -> o) -> (i -> o)))" in {
        FunctionType( Ti -> To, ( Ti -> To ) :: ( Ti -> To ) :: Nil ) must beLike { case FunctionType( To, ( Ti -> To ) :: ( Ti -> To ) :: Ti :: Nil ) => ok }
      }
    }
  }
}
