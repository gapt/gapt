/** 
 * Description: 
**/

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import scala.xml._
import at.logic.language.hol.HigherOrderLogic._
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.hol.LogicSymbols.{ConstantStringSymbol, VariableStringSymbol}
import at.logic.language.lambda.Types.TAImplicitConverters._
import at.logic.language.lambda.Symbols.SymbolImplicitConverters._
import at.logic.calculi.lk.LK._

case class beDeeplyEqual[T](a: Array[T]) extends Matcher[Array[T]]() {
  def apply(v: => Array[T]) = ( v.deepEquals(a), "successful deepEquals", v.deepToString + " not deepEquals " + a.deepToString )
}

class XMLParserTest extends Specification with JUnit {
  "XMLParser" should {
    "parse correctly a constant c" in {
      (new NodeReader(<constant symbol="c"/>) with XMLTermParser).getTerm() must beEqual(
        Var[HOL](new ConstantStringSymbol("c"), "i")
        )
    }
    "parse correctly a constant c from a StringReader" in {
      (new XMLReader(
        new java.io.StringReader("<constant symbol=\"c\"/>")) with XMLTermParser).getTerm() must beEqual(
          Var[HOL](new ConstantStringSymbol("c"), "i")
        )
    }
    "parse correctly a term g(c)" in {
      (new NodeReader(<function symbol="g">
                        <constant symbol="c"/>
                      </function>) with XMLTermParser).getTerm() must beEqual(
                    AppN(Var[HOL](new ConstantStringSymbol("g"),"(i -> i)"), Var[HOL](new ConstantStringSymbol("c"), "i")::Nil)
                )
    }
    "parse correctly a variable x" in {
      (new NodeReader(<variable symbol="x"></variable>) with XMLTermParser).getTerm() must beEqual (
        Var[HOL]("x", "i"))

    }
    "parse correctly a variablelist x,y,z" in {
      (new NodeReader(<variablelist>
                        <variable symbol="x"/>
                        <variable symbol="y"/>
                        <variable symbol="z"/>
                      </variablelist>) with XMLVariableListParser).getVariableList() must beEqual (
                    Var[HOL]("x", "i")::Var[HOL]("y", "i")::Var[HOL]("z", "i")::Nil
                  )
    }
    "parse correctly a term f(x,c)" in {
      (new NodeReader(<function symbol="f">
                        <variable symbol="x"/>
                        <constant symbol="c"/>
                      </function>) with XMLTermParser).getTerm() must beEqual (
                    AppN(Var[HOL](new ConstantStringSymbol("f"), "(i -> ( i -> i ))"),
                         Var[HOL]("x", "i")::Var[HOL](new ConstantStringSymbol("c"), "i")::Nil)
                )
    }
    "parse correctly an atom formula P(f(x,c),y)" in {
      (new NodeReader(<constantatomformula symbol="P">
                        <function symbol="f">
                          <variable symbol="x"/>
                          <constant symbol="c"/>
                        </function>
                        <variable symbol="y"/>
                      </constantatomformula>) with XMLFormulaParser).getFormula() must beEqual(
                      // FIXME: remove cast!
                      Atom("P",
                        AppN(Var[HOL](new ConstantStringSymbol("f"), "(i -> (i -> i))"),
                           Var[HOL]("x", "i")::Var[HOL](new ConstantStringSymbol("c"), "i")::Nil)
                         ::Var[HOL]("y", "i")::Nil))

    }
    "parse correctly a conjunction of atoms P and Q" in {
      (new NodeReader(<conjunctiveformula type="and">
                        <constantatomformula symbol="P"/>
                        <constantatomformula symbol="Q"/>
                      </conjunctiveformula>) with XMLFormulaParser).getFormula() must beEqual(
                    And(Atom("P", (Nil: List[LambdaExpression[HOL]])), Atom("Q", (Nil: List[LambdaExpression[HOL]]))))
    }
    "parse correctly a quantified formula (exists x) x = x" in {
      (new NodeReader(<quantifiedformula type="exists">
                        <variable symbol="x"/>
                        <constantatomformula symbol="=">
                          <variable symbol="x"/>
                          <variable symbol="x"/>
                        </constantatomformula>
                      </quantifiedformula>) with XMLFormulaParser).getFormula() must beEqual(
                    ExVar(Var[HOL]("x", "i"), 
                      Atom(new ConstantStringSymbol("="), Var[HOL]("x", "i")::Var[HOL]("x", "i")::Nil))
                )
    }
    "parse correctly a second-order variable X" in {
      (new NodeReader(<secondordervariable symbol="X"/>) with XMLSetTermParser).getSetTerm() must
      beEqual(Var[HOL](new VariableStringSymbol("X"), "(i -> o)"))
    }
    "parse correctly a variable atom formula X(c)" in {
      (new NodeReader(<variableatomformula>
                        <secondordervariable symbol="X"/>
                        <constant symbol="c"/>
                      </variableatomformula>) with XMLFormulaParser).getFormula() must beEqual(
                    Atom(new VariableStringSymbol("X"),
                         Var[HOL](new ConstantStringSymbol("c"), "i")::Nil)
                  )
    }
    "parse correctly a second-order quantified formula (all Z)Z(c)" in {
      (new NodeReader(<secondorderquantifiedformula type="all">
                        <secondordervariable symbol="Z"/>
                        <variableatomformula>
                          <secondordervariable symbol="Z"/>
                          <constant symbol="c"/>
                        </variableatomformula>
                      </secondorderquantifiedformula>) with XMLFormulaParser).getFormula() must beEqual(
                    AllVar(Var[HOL](new VariableStringSymbol("Z"), "(i -> o)"),
                      Atom(new VariableStringSymbol("Z"),
                           Var[HOL](new ConstantStringSymbol("c"), "i")::Nil))
                  )
    }
    "parse correctly a LambdaExpression lambda x . P(x)" in {
      (new NodeReader(<lambdasubstitution>
                        <variablelist>
                          <variable symbol="x"/>
                        </variablelist>
                        <constantatomformula symbol="P">
                          <variable symbol="x"/>
                        </constantatomformula>
                      </lambdasubstitution>) with XMLSetTermParser).getSetTerm() must beEqual(
                  Abs(Var[HOL]("x", "i"), Atom("P", Var[HOL]("x", "i")::Nil)))
    }
    "parse correctly a LambdaExpression lambda x,y. R(x,y)" in {
      (new NodeReader(<lambdasubstitution>
                        <variablelist>
                          <variable symbol="x"/>
                          <variable symbol="y"/>
                        </variablelist>
                        <constantatomformula symbol="R">
                          <variable symbol="x"/>
                          <variable symbol="y"/>
                        </constantatomformula>
                      </lambdasubstitution>) with XMLSetTermParser).getSetTerm() must beEqual(
                    AbsN(Var[HOL]("x", "i")::Var[HOL]("y", "i")::Nil,
                         Atom("R", Var[HOL]("x", "i")::Var[HOL]("y", "i")::Nil)))
    }
    "parse correctly a defined set \\cap(X, Y)" in {
      (new NodeReader(<definedset symbol="\cap" definition="\cap">
                        <secondordervariable symbol="X"/>
                        <secondordervariable symbol="Y"/>
                      </definedset>) with XMLSetTermParser).getSetTerm() must beEqual(
                    AppN( Var[HOL]( new ConstantStringSymbol("\\cap"),
                                    "((i -> o) -> ((i -> o) -> (i -> o)))"),
                          Var[HOL]( new VariableStringSymbol("X"), "(i -> o)" )::
                          Var[HOL]( new VariableStringSymbol("Y"), "(i -> o)" )::Nil)
                  )
    }
    "parse correctly a defined set formula \\cup(X,Y)(c)" in {
      (new NodeReader(<definedsetformula>
                        <definedset symbol="\cup" definition="\cup">
                          <secondordervariable symbol="X"/>
                          <secondordervariable symbol="Y"/>
                        </definedset>
                        <constant symbol="c"/>
                      </definedsetformula>) with XMLFormulaParser).getFormula() must beEqual(
                    App(AppN( Var[HOL]( new ConstantStringSymbol("\\cup"),
                                        "((i -> o) -> ((i -> o) -> (i -> o)))"),
                               Var[HOL]( new VariableStringSymbol("X"), "(i -> o)" )::
                               Var[HOL]( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
                        Var[HOL]( new ConstantStringSymbol("c"), "i" ) ) )
    }
    "parse correctly a complex sentence (all X)(all Y)(all z) X(z) impl \\cup(X,Y)(z)" in {
      (new NodeReader(<secondorderquantifiedformula type="all">
                        <secondordervariable symbol="X"/>
                        <secondorderquantifiedformula type="all">
                          <secondordervariable symbol="Y"/>
                          <quantifiedformula type="all">
                            <variable symbol="z"/>
                            <conjunctiveformula type="impl">
                              <variableatomformula>
                                <secondordervariable symbol="X"/>
                                <variable symbol="z"/>
                              </variableatomformula>
                              <definedsetformula>
                                <definedset symbol="\cup" definition="\cup">
                                  <secondordervariable symbol="X"/>
                                  <secondordervariable symbol="Y"/>
                                </definedset>
                                <variable symbol="z"/>
                              </definedsetformula>
                            </conjunctiveformula>
                          </quantifiedformula>
                        </secondorderquantifiedformula>
                      </secondorderquantifiedformula>) with XMLFormulaParser).getFormula() must beEqual(
                    AllVar( Var[HOL]( new VariableStringSymbol("X"), "(i -> o)" ),
                      AllVar( Var[HOL]( new VariableStringSymbol("Y"), "(i -> o)"),
                        AllVar( Var[HOL]( new VariableStringSymbol("z"), "i"),
                          Imp( Atom( new VariableStringSymbol("X"), Var[HOL]( "z", "i" )::Nil ),
                            App(AppN( Var[HOL]( new ConstantStringSymbol("\\cup"),
                                               "((i -> o) -> ((i -> o) -> (i -> o)))"),
                                       Var[HOL]( new VariableStringSymbol("X"), "(i -> o)" )::
                                       Var[HOL]( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
                                Var[HOL]( "z", "i" ) ).asInstanceOf[LambdaExpression[HOL] with Formula[HOL]] ) ) ) )
                  )
    }
    "parse correctly a sequent A, B :- C, D" in {
      (new NodeReader(<sequent>
                        <formulalist>
                          <constantatomformula symbol="A"/>
                          <constantatomformula symbol="B"/>
                        </formulalist>
                        <formulalist>
                          <constantatomformula symbol="C"/>
                          <constantatomformula symbol="D"/>
                        </formulalist>
                      </sequent>) with XMLSequentParser).getSequent() must beEqual(
                    Sequent(Atom("A", Nil : List[HOLTerm])::Atom("B", Nil : List[HOLTerm])::Nil,
                            Atom("C", Nil : List[HOLTerm])::Atom("D", Nil : List[HOLTerm])::Nil))
    }
    "parse correctly an axiom P :- P" in {
      (new NodeReader(<proof symbol="p" calculus="LK">
                        <rule type="axiom">
                          <sequent>
                            <formulalist>
                              <constantatomformula symbol="P"/>
                            </formulalist>
                            <formulalist>
                              <constantatomformula symbol="P"/>
                            </formulalist>
                          </sequent>
                        </rule>
                      </proof>) with XMLProofParser).getProof() must
                      beLike{ case Axiom( conc ) => true }
    }
    "parse a permutation parameter (1 2)" in {
      XMLUtils.permStringToCycles("(1 2)", 2) must
        beDeeplyEqual( (2::1::Nil).map(i => i - 1).toArray )
    }
    "parse a permutation parameter (1 2 3)(5 6)" in {
      XMLUtils.permStringToCycles("(1 2 3)(5 6)", 6) must
        beDeeplyEqual( (2::3::1::4::6::5::Nil).map( i => i - 1 ).toArray )
    }
    "parse a permutation rule" in {
      (new NodeReader(<rule type="permr" param="(1 3)(2)">
                        <sequent>
                          <formulalist>
                            <constantatomformula symbol="A"/>
                            <constantatomformula symbol="B"/>
                          </formulalist>
                          <formulalist>
                            <constantatomformula symbol="E"/>
                            <constantatomformula symbol="D"/>
                            <constantatomformula symbol="C"/>
                          </formulalist>
                        </sequent>
                        <rule type="axiom">
                          <sequent>
                          <formulalist>
                            <constantatomformula symbol="A"/>
                            <constantatomformula symbol="B"/>
                          </formulalist>
                          <formulalist>
                            <constantatomformula symbol="C"/>
                            <constantatomformula symbol="D"/>
                            <constantatomformula symbol="E"/>
                          </formulalist>
                        </sequent>
                      </rule>
                    </rule>) with XMLProofParser).getProof() must
                    beLike{ case Axiom( conc ) => true }
    }
    "parse correctly a proof of A, A :- A and A" in {
      (new NodeReader(<proof symbol="p" calculus="LK">
                        <rule type="andr">
                          <sequent>
                            <formulalist>
                              <constantatomformula symbol="A"/>
                              <constantatomformula symbol="A"/>
                            </formulalist>
                            <formulalist>
                              <conjunctiveformula type="and">
                                <constantatomformula symbol="A"/>
                                <constantatomformula symbol="A"/>
                              </conjunctiveformula>
                            </formulalist>
                          </sequent>
                          <rule type="axiom">
                            <sequent>
                              <formulalist>
                                <constantatomformula symbol="A"/>
                              </formulalist>
                              <formulalist>
                                <constantatomformula symbol="A"/>
                              </formulalist>
                            </sequent>
                          </rule>
                          <rule type="axiom">
                            <sequent>
                              <formulalist>
                                <constantatomformula symbol="A"/>
                              </formulalist>
                              <formulalist>
                                <constantatomformula symbol="A"/>
                              </formulalist>
                            </sequent>
                          </rule>
                        </rule>
                      </proof>) with XMLProofParser).getProof() must
                    beLike{ case AndRightRule( a1, a2, conc, aux1, aux2, p ) => true }
    }
    "parse correctly a proof with logical rules and permutations" in {
      (new NodeReader(<proof symbol="p" calculus="LK">
                        <rule type="orr1">
                          <sequent>
                            <formulalist/>
                            <formulalist>
                              <conjunctiveformula type="or">
                                <constantatomformula symbol="A"/>
                                <constantatomformula symbol="C"/>
                              </conjunctiveformula>
                              <conjunctiveformula type="or">
                                <constantatomformula symbol="B"/>
                                <constantatomformula symbol="D"/>
                              </conjunctiveformula>
                            </formulalist>
                          </sequent>
                          <rule type="perml" param="(1 2)">
                            <sequent>
                              <formulalist/>
                              <formulalist>
                                <conjunctiveformula type="or">
                                  <constantatomformula symbol="A"/>
                                  <constantatomformula symbol="C"/>
                                </conjunctiveformula>
                                <constantatomformula symbol="B"/>
                              </formulalist>
                            </sequent>
                            <rule type="orr1">
                              <sequent>
                                <formulalist/>
                                <formulalist>
                                  <constantatomformula symbol="B"/>
                                  <conjunctiveformula type="or">
                                    <constantatomformula symbol="A"/>
                                    <constantatomformula symbol="C"/>
                                  </conjunctiveformula>
                                </formulalist>
                              </sequent>
                              <rule type="perml" param="(1 2)">
                                <sequent>
                                  <formulalist/>
                                  <formulalist>
                                    <constantatomformula symbol="B"/>
                                    <constantatomformula symbol="A"/>
                                  </formulalist>
                                </sequent>
                                <rule type="axiom">
                                  <sequent>
                                    <formulalist/>
                                    <formulalist>
                                      <constantatomformula symbol="A"/>
                                      <constantatomformula symbol="B"/>
                                    </formulalist>
                                  </sequent>
                                </rule>
                              </rule>
                            </rule>
                          </rule>
                        </rule>
                      </proof>) with XMLProofParser).getProof().root.succedent must beEqual(
                        Or(Atom("A", (Nil: List[LambdaExpression[HOL]])),
                           Atom("C", (Nil: List[LambdaExpression[HOL]])))::
                        Or(Atom("B", (Nil: List[LambdaExpression[HOL]])),
                           Atom("D", (Nil: List[LambdaExpression[HOL]])))::Nil)
    }
  }
}
