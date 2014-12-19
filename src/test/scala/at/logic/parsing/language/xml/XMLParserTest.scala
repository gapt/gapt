/** 
 * Description: 
**/

package at.logic.parsing.language.xml

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import scala.xml._
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences.factory
import at.logic.calculi.lk.base.FSequent
import java.io.{FileInputStream, InputStreamReader}
import java.io.File.separator
import java.util.zip.GZIPInputStream
import org.specs2.matcher.Matcher
import org.specs2.matcher.Expectable
import at.logic.language.lambda.types._

case class beDeeplyEqual[T](a: Array[T]) extends Matcher[Array[T]]() {
  def apply[S <: Array[T]](v: Expectable[S]) = result( v.value.deep.equals(a.deep), "successful deepEquals", v.value.deep.toString + " not deepEquals " + a.deep.toString,v )
}

@RunWith(classOf[JUnitRunner])
class XMLParserTest extends SpecificationWithJUnit {

  implicit def fo2occ(f:HOLFormula) = factory.createFormulaOccurrence(f, Nil)
  implicit def fseq2seq(s : FSequent) = Sequent(s._1 map fo2occ, s._2 map fo2occ  )
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = fo2occ(pcf(sym))
  def pcf( sym: String ) = Atom( HOLConst( sym, To ), List() )

  "XMLParser" should {
    "parse correctly a constant c" in {
      (new NodeReader(<constant symbol="c"/>) with XMLTermParser).getTerm() must beEqualTo(
        HOLConst("c", Ti)
        )
    }
    "parse correctly a constant c from a StringReader" in {
      (new XMLReader(
        new java.io.StringReader("<constant symbol=\"c\"/>")) with XMLTermParser).getTerm() must beEqualTo(
          HOLConst("c", Ti)
        )
    }
    "parse correctly a term g(c)" in {
      (new NodeReader(<function symbol="g">
                        <constant symbol="c"/>
                      </function>) with XMLTermParser).getTerm() must beEqualTo(
                    HOLApp(HOLConst("g",Ti -> Ti), HOLConst("c", Ti))
                )
    }
    "parse correctly a variable x" in {
      (new NodeReader(<variable symbol="x"></variable>) with XMLTermParser).getTerm() must beEqualTo (
        HOLVar("x", Ti))

    }
    "parse correctly a variablelist x,y,z" in {
      (new NodeReader(<variablelist>
                        <variable symbol="x"/>
                        <variable symbol="y"/>
                        <variable symbol="z"/>
                      </variablelist>) with XMLVariableListParser).getVariableList() must beEqualTo (
                    HOLVar("x", Ti)::HOLVar("y", Ti)::HOLVar("z", Ti)::Nil
                  )
    }
    "parse correctly a term f(x,c)" in {
      (new NodeReader(<function symbol="f">
                        <variable symbol="x"/>
                        <constant symbol="c"/>
                      </function>) with XMLTermParser).getTerm() must beEqualTo (
                    Function(HOLConst("f", Ti -> (Ti -> Ti)),
                         HOLVar("x", Ti)::HOLConst("c", Ti)::Nil)
                )
    }
    "parse correctly an atom formula P(f(x,c),y)" in {
      (new NodeReader(<constantatomformula symbol="P">
                        <function symbol="f">
                          <variable symbol="x"/>
                          <constant symbol="c"/>
                        </function>
                        <variable symbol="y"/>
                      </constantatomformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                      Atom(HOLConst("P", Ti -> (Ti -> To)),
                        Function(HOLConst("f", Ti -> (Ti -> Ti)),
                           HOLVar("x", Ti)::HOLConst("c", Ti)::Nil)
                         ::HOLVar("y", Ti)::Nil))

    }
    "parse correctly a conjunction of atoms P and Q" in {
      (new NodeReader(<conjunctiveformula type="and">
                        <constantatomformula symbol="P"/>
                        <constantatomformula symbol="Q"/>
                      </conjunctiveformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                    And(pcf("P"), pcf("Q")))
    }
    "parse correctly a quantified formula (exists x) x = x" in {
      (new NodeReader(<quantifiedformula type="exists">
                        <variable symbol="x"/>
                        <constantatomformula symbol="=">
                          <variable symbol="x"/>
                          <variable symbol="x"/>
                        </constantatomformula>
                      </quantifiedformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                    ExVar(HOLVar("x", Ti),
                      Equation(HOLVar("x", Ti), HOLVar("x", Ti)))
                )
    }
    "parse correctly a second-order variable X" in {
      (new NodeReader(<secondordervariable symbol="X"/>) with XMLSetTermParser).getSetTerm() must
      beEqualTo(HOLVar("X", Ti -> To))
    }
    "parse correctly a variable atom formula X(c)" in {
      (new NodeReader(<variableatomformula>
                        <secondordervariable symbol="X"/>
                        <constant symbol="c"/>
                      </variableatomformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                    Atom(HOLVar("X", Ti -> To),
                         HOLConst("c", Ti)::Nil)
                  )
    }
    "parse correctly a second-order quantified formula (all Z)Z(c)" in {
      (new NodeReader(<secondorderquantifiedformula type="all">
                        <secondordervariable symbol="Z"/>
                        <variableatomformula>
                          <secondordervariable symbol="Z"/>
                          <constant symbol="c"/>
                        </variableatomformula>
                      </secondorderquantifiedformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                    AllVar(HOLVar("Z", Ti -> To),
                      Atom(HOLVar("Z", Ti -> To),
                           HOLConst("c", Ti)::Nil))
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
                      </lambdasubstitution>) with XMLSetTermParser).getSetTerm() must beEqualTo(
                  HOLAbs(HOLVar("x", Ti), Atom(HOLConst("P", Ti -> To), HOLVar("x", Ti)::Nil)))
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
                      </lambdasubstitution>) with XMLSetTermParser).getSetTerm() must beEqualTo(
                    HOLAbs(HOLVar("x", Ti),
                      HOLAbs(HOLVar("y", Ti),
                         Atom(HOLConst("R", Ti -> (Ti -> To)), HOLVar("x", Ti)::HOLVar("y", Ti)::Nil)))
      )
    }
    "parse correctly a defined set \\cap(X, Y)" in {
      (new NodeReader(<definedset symbol="\cap" definition="\cap">
                        <secondordervariable symbol="X"/>
                        <secondordervariable symbol="Y"/>
                      </definedset>) with XMLSetTermParser).getSetTerm() must beEqualTo(
                    Function( HOLConst( "\\cap",
                                    (Ti -> To) -> ((Ti -> To) -> (Ti -> To))),
                          HOLVar( "X", Ti -> To )::
                          HOLVar( "Y", Ti -> To )::Nil)
                  )
    }
    "parse correctly a defined set formula \\cup(X,Y)(c)" in {
      (new NodeReader(<definedsetformula>
                        <definedset symbol="\cup" definition="\cup">
                          <secondordervariable symbol="X"/>
                          <secondordervariable symbol="Y"/>
                        </definedset>
                        <constant symbol="c"/>
                      </definedsetformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                    HOLApp(Function( HOLConst( "\\cup",
                                        (Ti -> To) -> ((Ti -> To) -> (Ti -> To))),
                               HOLVar( "X", Ti -> To )::
                               HOLVar( "Y", Ti -> To )::Nil),
                        HOLConst( "c", Ti ) ) )
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
                      </secondorderquantifiedformula>) with XMLFormulaParser).getFormula() must beEqualTo(
                    AllVar( HOLVar( "X", Ti -> To ),
                      AllVar( HOLVar( "Y", Ti -> To),
                        AllVar( HOLVar( "z", Ti),
                          Imp( Atom( HOLVar("X", Ti -> To), HOLVar( "z", Ti )::Nil ),
                            (HOLApp(Function( HOLConst( "\\cup",
                                               (Ti -> To) -> ((Ti -> To) -> (Ti -> To))),
                                       HOLVar( "X", Ti -> To )::
                                       HOLVar( "Y", Ti -> To )::Nil),
                                HOLVar( "z", Ti ) ) ).asInstanceOf[HOLFormula] ) ) ) //TODO: cast should not be neccessary
                  ))
    }
    // BUG in specs2
    /*
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
    }*/
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
                              => ok }
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
                    beLike{ case Axiom( conc ) => ok }
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
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("xml" + separator + "test3.xml"))) with XMLProofDatabaseParser).getProofDatabase().proofs
      proofs.size must beEqualTo(1)
      proofs.head._2.root must beSyntacticMultisetEqual(
        Sequent(Nil, pc("A")::pc("C")::pc("F")::
                     fo2occ(And(pcf("B"), pcf("E")))::
                     fo2occ(Or(pcf("D"), pcf("G")))::Nil))
    }
    "parse correctly a proof with two orr1 rules and two permr rules from a file" in {
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("xml" + separator + "test2.xml"))) with XMLProofDatabaseParser).getProofDatabase().proofs
      proofs.size must beEqualTo(1)
      proofs.head._2.root must beSyntacticMultisetEqual(
                        Sequent(Nil, fo2occ(Or(pcf("A"), pcf("C")))::
                        fo2occ(Or(pcf("B"), pcf("D")))::Nil))
    }
    "parse correctly an involved proof from a file" in {
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("xml" + separator + "test1.xml"))) with XMLProofDatabaseParser).getProofDatabase().proofs
      val X = HOLVar( "X" , Ti -> To )
      val t = HOLConst( "t" , Ti)
      val s = HOLConst( "s" , Ti)
      val r = HOLConst( "r" , Ti)
      val f = HOLConst( "f" , Ti -> Ti)
      val x = HOLVar( "x" , Ti )
      val Rs = HOLConst( "R", Ti -> (Ti -> To) )
      val f1 = AllVar( X, And( Atom( X, t::Nil ), Neg( Atom( X, s::Nil ) ) ) )
      val f2 = And( Imp( Atom( Rs, r::t::Nil ), Atom( Rs, r::HOLApp( f, t )::Nil ) ),
                    ExVar( x, And( Atom( Rs, x::s::Nil ), Neg( Atom( Rs, x::HOLApp( f, s )::Nil ) ) ) ) )

      proofs.size must beEqualTo(1)
      proofs.head._2.root must beSyntacticMultisetEqual( Sequent( f1::Nil, f2::Nil ) )
    }

    "parse correctly a sequentlist from a gzipped file" in {
      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(getClass.getClassLoader.getResourceAsStream("xml" + separator + "slist.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()

      proofdb.sequentLists.size must beEqualTo(1)
    }
    "parse correctly a proof with definitions from a gzipped file" in {
      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(getClass.getClassLoader.getResourceAsStream("xml" + separator + "prime1-0.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()

      proofdb.Definitions.size must beEqualTo(21)
    }
  }
}
