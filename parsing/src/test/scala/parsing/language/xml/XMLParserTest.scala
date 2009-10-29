/** 
 * Description: 
**/

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers._
import at.logic.syntax.language.fol._
import scala.xml._

class XMLParserTest extends Specification with JUnit {
  "XMLParser" should {
    "parse correctly a variable" in {
      (new NodeReader(<variable symbol="x"></variable>) with XMLFOLTermParser).getTerm() must beEqual (Variable("x"))
    }
    "parse correctly a constant" in {
      (new NodeReader(<constant symbol="c"/>) with XMLFOLTermParser).getTerm() must beEqual(Constant("c"))
    }
    "parse correctly a function" in {
      (new NodeReader(<function symbol="f">
                        <variable symbol="x"/>
                        <constant symbol="c"/>
                      </function>) with XMLFOLTermParser).getTerm() must beEqual (Function("f", Variable("x")::Constant("c")::Nil))
    }
    "parse correctly an atom formula" in {
      (new NodeReader(<constantatomformula symbol="P">
                        <function symbol="f">
                          <variable symbol="x"/>
                          <constant symbol="c"/>
                        </function>
                        <variable symbol="y"/>
                      </constantatomformula>) with XMLFOLFormulaParser).getFormula() must beEqual(Atom("P", Function("f", Variable("x")::Constant("c")::Nil)::Variable("y")::Nil))

    }
    "parse correctly a conjunction of atoms" in {
      (new NodeReader(<conjunctiveformula type="and">
                        <constantatomformula symbol="P"/>
                        <constantatomformula symbol="Q"/>
                      </conjunctiveformula>) with XMLFOLFormulaParser).getFormula() must beEqual(And(Atom("P", Nil), Atom("Q", Nil)))
    }
  }
}
