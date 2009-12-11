/*
 * HOLTermExporterTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.xml

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import scala.xml._

import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.lkSpecs.beMultisetEqual
import at.logic.calculi.lk.base._
import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator
import at.logic.parsing.language.xml._
import scala.xml.Utility.trim

class HOLTermExporterTest extends SpecificationWithJUnit {
  
  val exporter = new HOLTermExporter{}
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = HOLConstFormula( new ConstantStringSymbol( sym ) )
  
  "HOLTermExporter" should {
    "export correctly a constant c" in {
      exporter.exportTerm(HOLConst(new ConstantStringSymbol("c"), "i")) must beEqual(<constant symbol="c"/>)
    }
    "export correctly a term g(c)" in {
      trim(exporter.exportTerm(AppN(HOLConst(new ConstantStringSymbol("g"),"(i -> i)"), HOLConst(new ConstantStringSymbol("c"), "i")::Nil))) must beEqual(<function symbol="g"><constant symbol="c"/></function>)
    }
    "export correctly a variable x" in {
      trim(exporter.exportTerm(HOLVar("x", "i"))) must beEqual (<variable symbol="x"></variable>)
    }
    "export correctly a term f(x,c)" in {
      trim(exporter.exportTerm(AppN(HOLConst(new ConstantStringSymbol("f"), "(i -> ( i -> i ))"),
          HOLVar("x", "i")::HOLConst(new ConstantStringSymbol("c"), "i")::Nil))) must beEqual (
        <function symbol="f"><variable symbol="x"/><constant symbol="c"/></function>
      )
    }
    "export correctly an atom formula P(f(x,c),y)" in {
      trim(exporter.exportTerm(Atom(new ConstantStringSymbol("P"), AppN(HOLConst(new ConstantStringSymbol("f"), "(i -> (i -> i))"),
          HOLVar("x", "i")::HOLConst(new ConstantStringSymbol("c"), "i")::Nil)::HOLVar("y", "i")::Nil))) must beEqual (trim(
        <constantatomformula symbol="P">
          <function symbol="f">
            <variable symbol="x"/>
            <constant symbol="c"/>
          </function>
          <variable symbol="y"/>
        </constantatomformula>
      ))
    }
    "export correctly a conjunction of atoms P and Q" in {
      trim(exporter.exportTerm(And(pc("P"), pc("Q")))) must beEqual (trim(
        <conjunctiveformula type="and">
         <constantatomformula symbol="P"/>
         <constantatomformula symbol="Q"/>
        </conjunctiveformula>
      ))
    }
    "export correctly a quantified formula (exists x) x = x" in {
      trim(exporter.exportTerm(ExVar(HOLVar("x", "i"), Atom(new ConstantStringSymbol("="), HOLVar("x", "i")::HOLVar("x", "i")::Nil)))) must beEqual (trim(
        <quantifiedformula type="exists">
          <variable symbol="x"/>
          <constantatomformula symbol="=">
            <variable symbol="x"/>
            <variable symbol="x"/>
          </constantatomformula>
        </quantifiedformula>
      ))
    }
    "export correctly a second-order variable X" in {
      trim(exporter.exportTerm(HOLVar(new VariableStringSymbol("X"), "(i -> o)"))) must beEqual (trim(
        <secondordervariable symbol="X"/>
      ))
    }
    "export correctly a variable atom formula X(c)" in {
      trim(exporter.exportTerm(Atom(new VariableStringSymbol("X"), HOLConst(new ConstantStringSymbol("c"), "i")::Nil))) must beEqual (trim(
        <variableatomformula>
          <secondordervariable symbol="X"/>
          <constant symbol="c"/>
        </variableatomformula>
      ))
    }
    "export correctly a second-order quantified formula (all Z)Z(c)" in {
      trim(exporter.exportTerm(AllVar(HOLVar(new VariableStringSymbol("Z"), "(i -> o)"), Atom(new VariableStringSymbol("Z"), HOLConst(new ConstantStringSymbol("c"), "i")::Nil)))) must beEqual (trim(
        <secondorderquantifiedformula type="all">
          <secondordervariable symbol="Z"/>
          <variableatomformula>
            <secondordervariable symbol="Z"/>
            <constant symbol="c"/>
          </variableatomformula>
        </secondorderquantifiedformula>
      ))
    }
    "export correctly a LambdaExpression lambda x . P(x)" in {
      trim(exporter.exportTerm(Abs(HOLVar("x", "i"), Atom(new ConstantStringSymbol("P"), HOLVar("x", "i")::Nil)))) must beEqual (trim(
        <lambdasubstitution>
          <variablelist>
            <variable symbol="x"/>
          </variablelist>
          <constantatomformula symbol="P">
            <variable symbol="x"/>
          </constantatomformula>
        </lambdasubstitution>
      ))
    }
    "export correctly a LambdaExpression lambda x,y. R(x,y)" in {
      trim(exporter.exportTerm(AbsN(HOLVar("x", "i")::HOLVar("y", "i")::Nil, Atom(new ConstantStringSymbol("R"), HOLVar("x", "i")::HOLVar("y", "i")::Nil)))) must beEqual (trim(
        <lambdasubstitution>
          <variablelist>
            <variable symbol="x"/>
            <variable symbol="y"/>
          </variablelist>
          <constantatomformula symbol="R">
            <variable symbol="x"/>
            <variable symbol="y"/>
          </constantatomformula>
        </lambdasubstitution>
      ))
    }
    "export correctly a defined set \\cap(X, Y)" in {
      trim(exporter.exportTerm(AppN( HOLConst( new ConstantStringSymbol("\\cap"),"((i -> o) -> ((i -> o) -> (i -> o)))"),
          HOLVar( new VariableStringSymbol("X"), "(i -> o)" ):: HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil))) must beEqual (trim(
        <definedset symbol="\cap" definition="\cap">
          <secondordervariable symbol="X"/>
          <secondordervariable symbol="Y"/>
        </definedset>
      ))
    }
    // definedsetformula is not supported yet
    /*"export correctly a defined set formula \\cup(X,Y)(c)" in {
      trim(exporter.exportTerm(App(AppN( HOLConst( new ConstantStringSymbol("\\cup"), "((i -> o) -> ((i -> o) -> (i -> o)))"),
          HOLVar( new VariableStringSymbol("X"), "(i -> o)" )::HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
          HOLConst( new ConstantStringSymbol("c"), "i" ) ))) must beEqual (trim(
        <definedsetformula>
          <definedset symbol="\cup" definition="\cup">
            <secondordervariable symbol="X"/>
            <secondordervariable symbol="Y"/>
          </definedset>
          <constant symbol="c"/>
        </definedsetformula>
      ))
    }
    "export correctly a complex sentence (all X)(all Y)(all z) X(z) impl \\cup(X,Y)(z)" in {
      trim(exporter.exportTerm(AllVar( HOLVar( new VariableStringSymbol("X"), "(i -> o)" ),
          AllVar( HOLVar( new VariableStringSymbol("Y"), "(i -> o)"),
            AllVar( HOLVar( new VariableStringSymbol("z"), "i"),
              Imp( Atom( new VariableStringSymbol("X"), HOLVar( "z", "i" )::Nil ),
                HOLAppFormula(AppN( HOLConst( new ConstantStringSymbol("\\cup"),
                                   "((i -> o) -> ((i -> o) -> (i -> o)))"),
                           HOLVar( new VariableStringSymbol("X"), "(i -> o)" )::
                           HOLVar( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
                    HOLVar( "z", "i" ) ) ) ) ) ) )) must beEqual (trim(
        <secondorderquantifiedformula type="all">
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
        </secondorderquantifiedformula>
      ))
    }*/
  }
}
    /*
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
                               if conc.getSequent.multisetEquals( Sequent( pc("P")::Nil,
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
      (new NodeReader(<rule type="contrl" param="2">
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
                      </rule>) with XMLProofParser).getProof().root.getSequent must beMultisetEqual(
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
                      </rule>) with XMLProofParser).getProof().root.getSequent must beMultisetEqual(
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
                      </proof>) with XMLProofParser).getProof().root.getSequent must beMultisetEqual(
                      Sequent(pc("A")::pc("A")::Nil, And(pc("A"), pc("A"))::Nil))
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
                      </proof>) with XMLProofParser).getProof().root.getSequent must beMultisetEqual(
                    Sequent(Nil, pc("B")::Or(pc("A"), pc("C"))::Nil))
    }
    "parse correctly a proof with some permutations, an andr, and an orr1 rule from a file" in {
      val proofs = (new XMLReader(new FileReader("target" + separator + "test-classes" + separator + "xml" + separator + "test3.xml")) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      proofs.first.root.getSequent must beMultisetEqual(
        Sequent(Nil, pc("A")::pc("C")::pc("F")::
                     And(pc("B"), pc("E"))::
                     Or(pc("D"), pc("G"))::Nil))
    }
    "parse correctly a proof with two orr1 rules and two permr rules from a file" in {
      val proofs = (new XMLReader(new FileReader("target" + separator + "test-classes" + separator + "xml" + separator + "test2.xml")) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
      proofs.first.root.getSequent must beMultisetEqual(
                        Sequent(Nil, Or(pc("A"),
                           pc("C"))::
                        Or(pc("B"),
                           pc("D"))::Nil))
    }
    "parse correctly an involved proof from a file" in {
      val proofs = (new XMLReader(new FileReader("target" + separator + "test-classes" + separator + "xml" + separator + "test1.xml")) with XMLProofDatabaseParser).getProofs()
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
      proofs.first.root.getSequent must beMultisetEqual( Sequent( f1::Nil, f2::Nil ) )
    }
    "parse correctly the second-order primeproof" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "xml" + separator + "prime2.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqual(1)
    }
  }*/

