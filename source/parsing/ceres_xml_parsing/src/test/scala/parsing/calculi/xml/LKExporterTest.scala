/*
 * LKExporterTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculus.xml

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import scala.xml._

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
import at.logic.calculi.lk.lkSpecs.beMultisetEqual
import at.logic.calculi.lk.base._
import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator
import at.logic.parsing.calculus.xml._
import scala.xml.Utility.trim
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.parsing.language.xml.HOLTermExporter

class LkExporterTest extends SpecificationWithJUnit {

  val exporter = new LKExporter{}
// helper to create 0-ary predicate constants
  def pc( sym: String ) = HOLConstFormula( new ConstantStringSymbol( sym ) )
  
  "LKExporter" should {
    "export correctly a sequent A, B :- C, D" in {
      trim(exporter.exportSequent(Sequent(pc("A")::pc("B")::Nil, pc("C")::pc("D")::Nil))) must beEqual (trim(
        <sequent>
          <formulalist>
            <constantatomformula symbol="A"/>
            <constantatomformula symbol="B"/>
          </formulalist>
          <formulalist>
            <constantatomformula symbol="C"/>
            <constantatomformula symbol="D"/>
          </formulalist>
        </sequent>
      ))
    }
  }
  "export correctly a sequent list {A1, B1 :- C1, D1, A2, B2 :- C2, D2}" in {
    trim(exporter.exportSequentList( "testlist", Sequent(pc("A1")::pc("B1")::Nil, pc("C1")::pc("D1")::Nil)::Sequent(pc("A2")::pc("B2")::Nil, pc("C2")::pc("D2")::Nil)::Nil)) must beEqual (trim(
        <sequentlist symbol="testlist">
          <sequent>
            <formulalist>
              <constantatomformula symbol="A1"/>
              <constantatomformula symbol="B1"/>
            </formulalist>
            <formulalist>
              <constantatomformula symbol="C1"/>
              <constantatomformula symbol="D1"/>
            </formulalist>
          </sequent>
          <sequent>
            <formulalist>
              <constantatomformula symbol="A2"/>
              <constantatomformula symbol="B2"/>
            </formulalist>
            <formulalist>
              <constantatomformula symbol="C2"/>
              <constantatomformula symbol="D2"/>
            </formulalist>
          </sequent>
        </sequentlist>
      ))
  }
}

/*
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

