/** 
 * Description: 
**/

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.parsing.language.prover9._
import at.logic.parsing.readers._
import at.logic.syntax.language.fol._

class FOLProver9TermParserTest extends Specification with JUnit {
  "FOLProver9TermParser" should {
    "parse correctly the string 'c'" in {
      (new StringReader("c") with FOLProver9TermParser).getTerm() must beEqual (Constant("c"))
    }
    "parse correctly the string '4'" in {
      (new StringReader("4") with FOLProver9TermParser).getTerm() must beEqual (Constant("4"))
    }
    "parse correctly the string 'x'" in {
      (new StringReader("x") with FOLProver9TermParser).getTerm() must beEqual (Variable("x"))
    }
    "parse correctly the string 'f(x)'" in {
      (new StringReader("f(x)") with FOLProver9TermParser).getTerm() must beEqual (Function("f",Variable("x")::Nil))
    }
    "parse correctly the string '+(4,x)'" in {
      (new StringReader("+(4,x)") with FOLProver9TermParser).getTerm() must beEqual (Function("+",Constant("4")::Variable("x")::Nil))
    }
    "parse correctly the string '(4) + (x)'" in {
      (new StringReader("(4)+(x)") with FOLProver9TermParser).getTerm() must beEqual (Function("+",Constant("4")::Variable("x")::Nil))
    }
    "parse correctly the string '(F(a)) | (G(b))'" in {
      (new StringReader("(F(a))|(G(b))") with FOLProver9TermParser).getTerm() must beEqual (Or(Atom("F",Constant("a")::Nil),Atom("G",Constant("b")::Nil)))
    }
    "parse correctly the string '(P(x)) | (-(Q(x)))'" in {
      (new StringReader("(P(x)) | (-(Q(x)))") with FOLProver9TermParser).getTerm() must beEqual (Or(Atom("P",Variable("x")::Nil),Not(Atom("Q",Variable("x")::Nil))))
    }
  }
}
