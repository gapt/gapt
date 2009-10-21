/** 
 * Description: 
**/

package at.logic.parsing.calculus.prover9

import org.specs._
import org.specs.runner._
import at.logic.parsing.language.prover9._
import at.logic.parsing.calculus.prover9._
import at.logic.parsing.readers._
import at.logic.syntax.calculus.resolution._
import at.logic.syntax.language.fol._

private class MyParser(str: String) extends StringReader(str) with FOLProver9TermParser with Prover9SequentsParser[Clause] with ClausesCreator
private object c1 extends Clause(ClauseTermOccurrence(Atom("P",Variable("x")::Nil))::Nil, ClauseTermOccurrence(Atom("Q", Variable("x")::Nil))::Nil)
private object c2 extends Clause(Nil, ClauseTermOccurrence(Atom("P", Constant("a")::Nil))::Nil)
class Prover9SequentsParserTest extends Specification with JUnit {
  "Prover9SequentsParser" should {
    "parse correctly the string '(P(x)) | (-(Q(x)))'" in {
      (new MyParser("(P(x)) | (-(Q(x))).")).getSequents() must beEqual (c1::Nil)
    }
    "parse correctly the string '|(P(x),-(Q(x)))'" in {
      (new MyParser("|(P(x),-(Q(x))).")).getSequents() must beEqual (c1::Nil)
    }
    "parse correctly the string '(P(x)) | (-(Q(x))).\n -(P(a)).'" in {
      (new MyParser("(P(x)) | (-(Q(x))). \n -(P(a)).")).getSequents() must beEqual (c1::c2::Nil)
    }
    "return an empty sequent on the string '.'" in {
      (new MyParser(".")).getSequents() must beEqual (Clause(Nil,Nil)::Nil)
    }
    "return an empty list on the empty string" in {
      (new MyParser("")).getSequents() must beEqual (Nil)
    }
  }
}
