/* Test cases for the term generator.
*/

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._

import org.specs._
import org.specs.runner._
import org.scalacheck._
import org.scalacheck.Prop._

import org.specs.matcher._

import at.logic.utils.testing.PropMatcher.bePassed

class termgeneratorTest extends SpecificationWithJUnit {
    "The generator " should {
        var generator = new FOLtermGenerator(123)

        "generate first order variables" in {
            //var v = FOLVar(new VariableStringSymbol("x"))
            generator.generateVariable match {
                case x:FOLVar => true must beEqual (true)
                case _ => true must beEqual (false)
            }
            
        }
    }
}