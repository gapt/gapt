/*
 * CommandsParserTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
/*
package at.logic.provers.atp.commandsParsers

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.typedLambdaCalculus._

private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL

class CommandsParserTest extends SpecificationWithJUnit {
  "FOLResolutionCommandsParser" should {
    "generate the right factors" in {
      val cparser = RobinsonCommandsParser
      "for the clause A(x) | A(a) | A(f(x)) | A(f(y)) with substitution x/f(b) and the resolved literal A(x)" in {
        val cls = new MyParser("A(f(b)) | A(a) | A(f(f(b))) | A(f(y)).").getClauseList.head.positive.asInstanceOf[List[FOLExpression]]
        val factors = cparser.computeFactors(cls, cls.indices.tail.toList, cls.head, Substitution[FOLExpression](), Nil)
        "- number of factors must be 1" in {
          factors.size must beEqual(1)
        }
        "- the returned list of formulas must contain only one formula A(f(y))" in {
          factors.head._1.size must beEqual(1)
          cls(factors.head._1.head) must beEqual(cls.last)
        }
        "- subsitution must be y/b" in {
          factors.head._2 must beEqual(Substitution(FOLVar(VariableStringSymbol("y")), FOLConst(ConstantStringSymbol("b"))))
        }
      }
      "for the clause A(f(f(a))) | A(f(x)) with  the resolved literal A(f(y))" in {
        val cls = new MyParser("A(f(y)) | A(f(f(a))) | A(f(x)).").getClauseList.head.positive.asInstanceOf[List[FOLExpression]]
        val factors = cparser.computeFactors(cls, cls.indices.tail.toList, cls.head, Substitution[FOLExpression](), Nil)
        "- number of factors must be 3" in {
          factors.size must beEqual(3)
        }
        "- the third element in the list must contain only: A(f(f(a)))" in {
          factors.tail.tail.head._1.size must beEqual(1)
          cls(factors.tail.tail.head._1.head) must beEqual(cls(1))
        }
        "- the second element in the list must contain only: A(f(x))" in {
          factors.tail.head._1.size must beEqual(1)
          cls(factors.tail.head._1.head) must beEqual(cls(2))
        }
        "- the first element in the list must contain only: A(f(f(a))),A(f(x))" in {
          factors.head._1.size must beEqual(2)
          cls(factors.head._1.head) must beEqual(cls(1))
          cls(factors.head._1.tail.head) must beEqual(cls(2))
        }
      }
    }
  }
  //def functionToString(fun: LambdaExpression => LambdaExpression, terms: List[LambdaExpression])  = terms.map(x => x.toString + "->" + fun(x).toString)
}
*/