/*
 * typedLambdaCalculusTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import org.specs._
import org.specs.runner._


class TypedLambdaCalculusTest extends Specification with JUnit {
  "TypedLambdaCalculus" should {
    "make implicit conversion from String to Name" in {
        import NameImplicitConverters._
        (Var[TInd]("p")) must beEqual (Var[TInd](Name("p")))
    }
  }
}
