/*
 * TermNormalizerTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.normalization

import org.specs2.mutable._
import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleHOLParser
import scala.collection.mutable.Map
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle

private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser
/*
@RunWith(classOf[JUnitRunner])
class TermNormalizerTest extends SpecificationWithJUnit {
  val f1a = new MyParser("And P(z:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
  val f1b = new MyParser("And P(x_{1}:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
  val f2a = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]
  val f2b = new MyParser("And P(f(x_{1}:i, x_{2}:i, a:i):(i->i), x_{3}:(i->i)) Q(Neg T(x_{1}:i, a:i, b:(i->i), g(x_{1}:i):i), Forall x_{4}: (i -> (i -> i)) a(x_{4}: (i -> (i -> i)), x_{1}: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]
  val f3a = Prover9TermParserLadrStyle.parseFormula("(all x P(x)) & (all x P(x))")

  "TermNormalizer" should {
    "normalize correctly the terms:" in {
      "1" in {
        var id = 0
        TermNormalizer(f1a,Map(), {id = id + 1; id}) must beEqualTo(f1b)
      }
      "2" in {
        var id = 0
        TermNormalizer(f2a,Map(), {id = id + 1; id}) must beEqualTo(f2b)
      }
      "3" in {
        var id = 0
        val t =TermNormalizer(f3a,Map(), {id = id + 1; id} )
        t match {
          case And(AllVar(x1,formula1), AllVar(x2,formula2)) =>
            x1 mustNotEqual(x2)
          case _ =>
            failure("Logical structure of " +f3a + " is not the same as "+t+"!")
        }
      }
    }
  }
}
*/