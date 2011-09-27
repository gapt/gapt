/** 
 * Description: 
**/

package at.logic.parsing.language.xml

import _root_.at.logic.calculi.lk.lkSpecs.{beSyntacticMultisetEqual, beMultisetEqual}
import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import scala.xml._

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences.factory
import at.logic.calculi.lk.base.types.FSequent

import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator
import java.util.zip.GZIPInputStream

case class beDeeplyEqual[T](a: Array[T]) extends Matcher[Array[T]]() {
  def apply(v: => Array[T]) = ( v.deep.equals(a.deep), "successful deepEquals", v.deep.toString + " not deepEquals " + a.deep.toString )
}

class XMLParserTest extends SpecificationWithJUnit {

  implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Nil)
  implicit def fseq2seq(s : FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = fo2occ(pcf(sym))
  def pcf( sym: String ) = Atom( new ConstantStringSymbol( sym ), List() )

  "XMLParser" should {
    "parse correctly a constant c" in {
      (new NodeReader(<constant symbol="c"/>) with XMLTermParser).getTerm() must beEqual(
        HOLConst(new ConstantStringSymbol("c"), "i")
        )
    }
    "parse correctly a constant c from a StringReader" in {
      (new XMLReader(
        new java.io.StringReader("<constant symbol=\"c\"/>")) with XMLTermParser).getTerm() must beEqual(
          HOLConst(new ConstantStringSymbol("c"), "i")
        )
    }
    "parse correctly a term g(c)" in {
      (new NodeReader(<function symbol="g">
                        <constant symbol="c"/>
                      </function>) with XMLTermParser).getTerm() must beEqual(
                    AppN(HOLConst(new ConstantStringSymbol("g"),"(i -> i)"), HOLConst(new ConstantStringSymbol("c"), "i")::Nil)
                )
    }
    "parse correctly a variable x" in {
      (new NodeReader(<variable symbol="x"></variable>) with XMLTermParser).getTerm() must beEqual (
        HOLVar("x", "i"))

    }
    "parse correctly a variablelist x,y,z" in {
      (new NodeReader(<variablelist>
                        <variable symbol="x"/>
                        <variable symbol="y"/>
                        <variable symbol="z"/>
                      </variablelist>) with XMLVariableListParser).getVariableList() must beEqual (
                    HOLVar("x", "i")::HOLVar("y", "i")::HOLVar("z", "i")::Nil
                  )
    }
    "parse correctly a term f(x,c)" in {
      (new NodeReader(<function symbol="f">
                        <variable symbol="x"/>
                        <constant symbol="c"/>
                      </function>) with XMLTermParser).getTerm() must beEqual (
                    AppN(HOLConst(new ConstantStringSymbol("f"), "(i -> ( i -> i ))"),
                         HOLVar("x", "i")::HOLConst(new ConstantStringSymbol("c"), "i")::Nil)
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
                      Atom(new ConstantStringSymbol("P"),
                        AppN(HOLConst(new ConstantStringSymbol("f"), "(i -> (i -> i))"),
                           HOLVar("x", "i")::HOLConst(new ConstantStringSymbol("c"), "i")::Nil)
                         ::HOLVar("y", "i")::Nil))

    }
    "parse correctly a conjunction of atoms P and Q" in {
      (new NodeReader(<conjunctiveformula type="and">
                        <constantatomformula symbol="P"/>
                        <constantatomformula symbol="Q"/>
                      </conjunctiveformula>) with XMLFormulaParser).getFormula() must beEqual(
                    And(pcf("P"), pcf("Q")))
    }
    "parse correctly a quantified formula (exists x) x = x" in {
      (new NodeReader(<quantifiedformula type="exists">
                        <variable symbol="x"/>
                        <constantatomformula symbol="=">
                          <variable symbol="x"/>
                          <variable symbol="x"/>
                        </constantatomformula>
                      </quantifiedformula>) with XMLFormulaParser).getFormula() must beEqual(
                    ExVar(HOLVar("x", "i"), 
                      Atom(new ConstantStringSymbol("="), HOLVar("x", "i")::HOLVar("x", "i")::Nil))
                )
    }
    "parse correctly a second-order variable X" in {
      (new NodeReader(<secondordervariable symbol="X"/>) with XMLSetTermParser).getSetTerm() must
      beEqual(HOLVar(new VariableStringSymbol("X"), "(i -> o)"))
    }
    "parse correctly a variable atom formula X(c)" in {
      (new NodeReader(<variableatomformula>
                        <secondordervariable symbol="X"/>
                        <constant symbol="c"/>
                      </variableatomformula>) with XMLFormulaParser).getFormula() must beEqual(
                    Atom(new VariableStringSymbol("X"),
                         HOLConst(new ConstantStringSymbol("c"), "i")::Nil)
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
                    AllVar(HOLVar(new VariableStringSymbol("Z"), "(i -> o)"),
                      Atom(new VariableStringSymbol("Z"),
                           HOLConst(new ConstantStringSymbol("c"), "i")::Nil))
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
                  Abs(HOLVar("x", "i"), Atom(new ConstantStringSymbol("P"), HOLVar("x", "i")::Nil)))
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
                    AbsN(HOLVar("x", "i")::HOLVar("y", "i")::Nil,
                         Atom(new ConstantStringSymbol("R"), HOLVar("x", "i")::HOLVar("y", "i")::Nil)))
    }
    "parse correctly a defined set \\cap(X, Y)" in {
      (new NodeReader(<definedset symbol="\cap" definition="\cap">
                        <secondordervariable symbol="X"/>
                        <secondordervariable symbol="Y"/>
                      </definedset>) with XMLSetTermParser).getSetTerm() must beEqual(
                    AppN( HOLConst( new ConstantStringSymbol("\\cap"),
                                    "((i -> o) -> ((i -> o) -> (i -> o)))"),
                          HOLVar( new VariableStringSymbol("X"), "(i -> o)" )::
                          HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil)
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
                    App(AppN( HOLConst( new ConstantStringSymbol("\\cup"),
                                        "((i -> o) -> ((i -> o) -> (i -> o)))"),
                               HOLVar( new VariableStringSymbol("X"), "(i -> o)" )::
                               HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
                        HOLConst( new ConstantStringSymbol("c"), "i" ) ) )
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
                    AllVar( HOLVar( new VariableStringSymbol("X"), "(i -> o)" ),
                      AllVar( HOLVar( new VariableStringSymbol("Y"), "(i -> o)"),
                        AllVar( HOLVar( new VariableStringSymbol("z"), "i"),
                          Imp( Atom( new VariableStringSymbol("X"), HOLVar( "z", "i" )::Nil ),
                            HOLAppFormula(AppN( HOLConst( new ConstantStringSymbol("\\cup"),
                                               "((i -> o) -> ((i -> o) -> (i -> o)))"),
                                       HOLVar( new VariableStringSymbol("X"), "(i -> o)" )::
                                       HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
                                HOLVar( "z", "i" ) ) ) ) ) )
                  )
    }
    "parse correctly a sequent A, B :- C, D" in {
      ((new NodeReader(<sequent>
                        <formulalist>
                          <constantatomformula symbol="A"/>
                          <constantatomformula symbol="B"/>
                        </formulalist>
                        <formulalist>
                          <constantatomformula symbol="C"/>
                          <constantatomformula symbol="D"/>
                        </formulalist>
                      </sequent>) with XMLSequentParser).getSequent()) must beSyntacticMultisetEqual(
                    Sequent(pc("A")::pc("B")::Nil,
                            pc("C")::pc("D")::Nil))
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
                      beLike{ case Axiom( conc )
                               if conc.syntacticMultisetEquals( Sequent( pc("P")::Nil,
                                                                pc("P")::Nil ))
                              => true }
    }
    "parse a permutation parameter (1 2)" in {
      XMLUtils.permStringToCycles("(1 2)", 2) must
        beDeeplyEqual( (2::1::Nil).map(i => i - 1).toArray )
    }
    "parse a permutation parameter (1 2 3)(5 6)" in {
      XMLUtils.permStringToCycles("(1 2 3)(5 6)", 6) must
        beDeeplyEqual( (3::1::2::4::6::5::Nil).map( i => i - 1 ).toArray )
    }
    "parse a permutation parameter (3 4 5) of size 5" in {
      XMLUtils.permStringToCycles("(3 4 5)", 5) must
        beDeeplyEqual( (1::2::5::3::4::Nil).map( i => i - 1 ).toArray )
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
    "parse a simple contraction rule" in {
      ((new NodeReader(<rule type="contrl" param="2">
                        <sequent>
                          <formulalist>
                            <constantatomformula symbol="A"/>
                          </formulalist>
                          <formulalist/>
                        </sequent>
                        <rule type="axiom">
                          <sequent>
                            <formulalist>
                              <constantatomformula symbol="A"/>
                              <constantatomformula symbol="A"/>
                            </formulalist>
                            <formulalist/>
                          </sequent>
                        </rule>
                      </rule>) with XMLProofParser).getProof().root) must beSyntacticMultisetEqual(
                      Sequent(pc("A")::Nil, Nil))
    }
    "parse an involved contraction rule" in {
      (new NodeReader(<rule type="contrl" param="2,1,2,1,1">
                        <sequent>
                          <formulalist>
                            <constantatomformula symbol="A"/>
                            <constantatomformula symbol="B"/>
                            <constantatomformula symbol="C"/>
                            <constantatomformula symbol="C"/>
                            <constantatomformula symbol="D"/>
                          </formulalist>
                          <formulalist/>
                        </sequent>
                        <rule type="axiom">
                          <sequent>
                            <formulalist>
                              <constantatomformula symbol="A"/>
                              <constantatomformula symbol="A"/>
                              <constantatomformula symbol="B"/>
                              <constantatomformula symbol="C"/>
                              <constantatomformula symbol="C"/>
                              <constantatomformula symbol="C"/>
                              <constantatomformula symbol="D"/>
                            </formulalist>
                            <formulalist/>
                          </sequent>
                        </rule>
                      </rule>) with XMLProofParser).getProof().root must beSyntacticMultisetEqual(
                      Sequent(pc("A")::pc("B")::pc("C")::pc("C")::pc("D")::Nil, Nil))
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
                      </proof>) with XMLProofParser).getProof().root must beSyntacticMultisetEqual(
                      Sequent(pc("A")::pc("A")::Nil, fo2occ(And(pcf("A"), pcf("A")))::Nil))
    }
    "parse correctly a proof with one orr1 rule and one permr rule" in {
      (new NodeReader(<proof symbol="p" calculus="LK">
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
                          <rule type="permr" param="(1 2)">
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
                      </proof>) with XMLProofParser).getProof().root must beSyntacticMultisetEqual(
                    Sequent(Nil, pc("B")::fo2occ(Or(pcf("A"), pcf("C")))::Nil))
    }
    "parse correctly a proof with some permutations, an andr, and an orr1 rule from a file" in {
      val proofs = (new XMLReader(new FileReader("target" + separator + "test-classes" + separator + "xml" + separator + "test3.xml")) with XMLProofDatabaseParser).getProofDatabase().proofs
      proofs.size must beEqual(1)
      proofs.head._2.root must beSyntacticMultisetEqual(
        Sequent(Nil, pc("A")::pc("C")::pc("F")::
                     fo2occ(And(pcf("B"), pcf("E")))::
                     fo2occ(Or(pcf("D"), pcf("G")))::Nil))
    }
    "parse correctly a proof with two orr1 rules and two permr rules from a file" in {
      val proofs = (new XMLReader(new FileReader("target" + separator + "test-classes" + separator + "xml" + separator + "test2.xml")) with XMLProofDatabaseParser).getProofDatabase().proofs
      proofs.size must beEqual(1)
      proofs.head._2.root must beSyntacticMultisetEqual(
                        Sequent(Nil, fo2occ(Or(pcf("A"), pcf("C")))::
                        fo2occ(Or(pcf("B"), pcf("D")))::Nil))
    }
    "parse correctly an involved proof from a file" in {
      val proofs = (new XMLReader(new FileReader("target" + separator + "test-classes" + separator + "xml" + separator + "test1.xml")) with XMLProofDatabaseParser).getProofDatabase().proofs
      val X = HOLVar( new VariableStringSymbol( "X" ), i -> o )
      val t = HOLConst( new ConstantStringSymbol( "t" ), i)
      val s = HOLConst( new ConstantStringSymbol( "s" ), i)
      val r = HOLConst( new ConstantStringSymbol( "r" ), i)
      val f = HOLConst( new ConstantStringSymbol( "f" ), i -> i)
      val x = HOLVar( new VariableStringSymbol( "x" ), i )
      val Rs = new ConstantStringSymbol( "R" )
      val f1 = AllVar( X, And( HOLAppFormula( X, t ), Neg( HOLAppFormula( X, s ) ) ) )
      val f2 = And( Imp( Atom( Rs, r::t::Nil ), Atom( Rs, r::HOLApp( f, t )::Nil ) ),
                    ExVar( x, And( Atom( Rs, x::s::Nil ), Neg( Atom( Rs, x::HOLApp( f, s )::Nil ) ) ) ) )

      proofs.size must beEqual(1)
      proofs.head._2.root must beSyntacticMultisetEqual( Sequent( f1::Nil, f2::Nil ) )
    }

    "parse correctly a sequentlist from a gzipped file" in {
      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "xml" + separator + "slist.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
     
      proofdb.sequentLists.size must beEqual(1)
    }
  }
}
