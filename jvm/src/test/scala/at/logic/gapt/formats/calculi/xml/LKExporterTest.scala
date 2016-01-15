/*
 * LKExporterTest.scala
 */

package at.logic.gapt.formats.calculi.xml

import at.logic.gapt.formats.xml.{ HOLTermXMLExporter, LKExporter }
import at.logic.gapt.proofs.HOLSequent
import org.specs2.mutable._

import scala.xml.Utility.trim

import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.expr._
import at.logic.gapt.expr.StringSymbol
import at.logic.gapt.expr.To

class LkExporterTest extends Specification {

  val exporter = new LKExporter {}
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = HOLAtom( Const( StringSymbol( sym ), To ), List() )

  "LKExporter" should {
    "export correctly a sequent A, B :- C, D" in {
      trim( exporter.exportSequent( HOLSequent( List( "A", "B" ) map ( pc ), List( "C", "D" ) map ( pc ) ) ) ) must beEqualTo( trim(
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
      ) )
    }

    "export correctly a sequent list {A1, B1 :- C1, D1, A2, B2 :- C2, D2}" in {
      trim( exporter.exportSequentList( "testlist", List(
        HOLSequent( List( "A1", "B1" ) map ( pc ), List( "C1", "D1" ) map ( pc ) ),
        HOLSequent( List( "A2", "B2" ) map ( pc ), List( "C2", "D2" ) map ( pc ) )
      ) ) ) must beEqualTo( trim(
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
      ) )
    }
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
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("xml" + separator + "test3.xml"))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqualTo(1)
      proofs.first.root.getSequent must beMultisetEqual(
        Sequent(Nil, pc("A")::pc("C")::pc("F")::
                     And(pc("B"), pc("E"))::
                     Or(pc("D"), pc("G"))::Nil))
    }
    "parse correctly a proof with two orr1 rules and two permr rules from a file" in {
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("xml" + separator + "test2.xml"))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqualTo(1)
      proofs.first.root.getSequent must beMultisetEqual(
                        Sequent(Nil, Or(pc("A"),
                           pc("C"))::
                        Or(pc("B"),
                           pc("D"))::Nil))
    }
    "parse correctly an involved proof from a file" in {
      val proofs = (new XMLReader(new InputStreamReader(getClass.getClassLoader.getResourceAsStream("xml" + separator + "test1.xml"))) with XMLProofDatabaseParser).getProofs()
      val X = Var( new VariableStringSymbol( "X" ), i -> o )
      val t = Const( new ConstantStringSymbol( "t" ), i)
      val s = Const( new ConstantStringSymbol( "s" ), i)
      val r = Const( new ConstantStringSymbol( "r" ), i)
      val f = Const( new ConstantStringSymbol( "f" ), i -> i)
      val x = Var( new VariableStringSymbol( "x" ), i )
      val Rs = new ConstantStringSymbol( "R" )
      val f1 = All( X, And( AppFormula( X, t ), Neg( AppFormula( X, s ) ) ) )
      val f2 = And( Imp( Atom( Rs, r::t::Nil ), Atom( Rs, r::App( f, t )::Nil ) ),
                    Ex( x, And( Atom( Rs, x::s::Nil ), Neg( Atom( Rs, x::App( f, s )::Nil ) ) ) ) )

      proofs.size must beEqualTo(1)
      proofs.first.root.getSequent must beMultisetEqual( Sequent( f1::Nil, f2::Nil ) )
    }
    "parse correctly the second-order primeproof" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "xml" + separator + "prime2.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      proofs.size must beEqualTo(1)
    }
  }*/

