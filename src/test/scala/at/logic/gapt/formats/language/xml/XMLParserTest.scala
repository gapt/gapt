
package at.logic.gapt.formats.expr.xml

import at.logic.gapt.formats.xml.XMLParser
import at.logic.gapt.proofs.{ SequentMatchers, HOLSequent }
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.occurrences.factory
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr._
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.expr._
import com.sun.org.apache.xml.internal.resolver.CatalogManager
import com.sun.org.apache.xml.internal.resolver.tools.CatalogResolver
import java.io.File.separator
import java.io.{ FileInputStream, InputStreamReader, ByteArrayInputStream }
import java.util.zip.GZIPInputStream
import org.specs2.matcher.Expectable
import org.specs2.matcher.Matcher
import org.specs2.mutable._
import org.xml.sax.ErrorHandler
import org.xml.sax.helpers.XMLReaderFactory
import scala.io.{ BufferedSource, Source }
import scala.xml.SAXParseException

class XMLParserTest extends Specification with SequentMatchers {

  implicit def fo2occ( f: HOLFormula ) = factory.createFormulaOccurrence( f, Nil )
  implicit def fseq2seq( s: HOLSequent ) = s map fo2occ
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = fo2occ( pcf( sym ) )
  def pcf( sym: String ) = HOLAtom( Const( sym, To ), List() )

  "XMLParser" should {
    "parse correctly a constant c" in {
      ( new NodeReader( <constant symbol="c"/> ) with XMLTermParser ).getTerm() must beEqualTo(
        Const( "c", Ti )
      )
    }
    "parse correctly a constant c from a StringReader" in {
      ( new XMLReader( new ByteArrayInputStream( "<constant symbol=\"c\"/>".getBytes( "UTF8" ) ) ) with XMLTermParser ).getTerm() must beEqualTo( Const( "c", Ti ) )
    }
    "parse correctly a term g(c)" in {
      ( new NodeReader( <function symbol="g">
                          <constant symbol="c"/>
                        </function> ) with XMLTermParser ).getTerm() must beEqualTo(
        App( Const( "g", Ti -> Ti ), Const( "c", Ti ) )
      )
    }
    "parse correctly a variable x" in {
      ( new NodeReader( <variable symbol="x"></variable> ) with XMLTermParser ).getTerm() must beEqualTo(
        Var( "x", Ti )
      )

    }
    "parse correctly a variablelist x,y,z" in {
      ( new NodeReader( <variablelist>
                          <variable symbol="x"/>
                          <variable symbol="y"/>
                          <variable symbol="z"/>
                        </variablelist> ) with XMLVariableListParser ).getVariableList() must beEqualTo(
        Var( "x", Ti ) :: Var( "y", Ti ) :: Var( "z", Ti ) :: Nil
      )
    }
    "parse correctly a term f(x,c)" in {
      ( new NodeReader( <function symbol="f">
                          <variable symbol="x"/>
                          <constant symbol="c"/>
                        </function> ) with XMLTermParser ).getTerm() must beEqualTo(
        HOLFunction(
          Const( "f", Ti -> ( Ti -> Ti ) ),
          Var( "x", Ti ) :: Const( "c", Ti ) :: Nil
        )
      )
    }
    "parse correctly an atom formula P(f(x,c),y)" in {
      ( new NodeReader( <constantatomformula symbol="P">
                          <function symbol="f">
                            <variable symbol="x"/>
                            <constant symbol="c"/>
                          </function>
                          <variable symbol="y"/>
                        </constantatomformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        HOLAtom(
          Const( "P", Ti -> ( Ti -> To ) ),
          HOLFunction(
            Const( "f", Ti -> ( Ti -> Ti ) ),
            Var( "x", Ti ) :: Const( "c", Ti ) :: Nil
          )
            :: Var( "y", Ti ) :: Nil
        )
      )

    }
    "parse correctly a conjunction of atoms P and Q" in {
      ( new NodeReader( <conjunctiveformula type="and">
                          <constantatomformula symbol="P"/>
                          <constantatomformula symbol="Q"/>
                        </conjunctiveformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        And( pcf( "P" ), pcf( "Q" ) )
      )
    }
    "parse correctly a quantified formula (exists x) x = x" in {
      ( new NodeReader( <quantifiedformula type="exists">
                          <variable symbol="x"/>
                          <constantatomformula symbol="=">
                            <variable symbol="x"/>
                            <variable symbol="x"/>
                          </constantatomformula>
                        </quantifiedformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        Ex(
          Var( "x", Ti ),
          Eq( Var( "x", Ti ), Var( "x", Ti ) )
        )
      )
    }
    "parse correctly a second-order variable X" in {
      ( new NodeReader( <secondordervariable symbol="X"/> ) with XMLSetTermParser ).getSetTerm() must
        beEqualTo( Var( "X", Ti -> To ) )
    }
    "parse correctly a variable atom formula X(c)" in {
      ( new NodeReader( <variableatomformula>
                          <secondordervariable symbol="X"/>
                          <constant symbol="c"/>
                        </variableatomformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        HOLAtom(
          Var( "X", Ti -> To ),
          Const( "c", Ti ) :: Nil
        )
      )
    }
    "parse correctly a second-order quantified formula (all Z)Z(c)" in {
      ( new NodeReader( <secondorderquantifiedformula type="all">
                          <secondordervariable symbol="Z"/>
                          <variableatomformula>
                            <secondordervariable symbol="Z"/>
                            <constant symbol="c"/>
                          </variableatomformula>
                        </secondorderquantifiedformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        All(
          Var( "Z", Ti -> To ),
          HOLAtom(
            Var( "Z", Ti -> To ),
            Const( "c", Ti ) :: Nil
          )
        )
      )
    }
    "parse correctly a LambdaExpression lambda x . P(x)" in {
      ( new NodeReader( <lambdasubstitution>
                          <variablelist>
                            <variable symbol="x"/>
                          </variablelist>
                          <constantatomformula symbol="P">
                            <variable symbol="x"/>
                          </constantatomformula>
                        </lambdasubstitution> ) with XMLSetTermParser ).getSetTerm() must beEqualTo(
        Abs( Var( "x", Ti ), HOLAtom( Const( "P", Ti -> To ), Var( "x", Ti ) :: Nil ) )
      )
    }
    "parse correctly a LambdaExpression lambda x,y. R(x,y)" in {
      ( new NodeReader( <lambdasubstitution>
                          <variablelist>
                            <variable symbol="x"/>
                            <variable symbol="y"/>
                          </variablelist>
                          <constantatomformula symbol="R">
                            <variable symbol="x"/>
                            <variable symbol="y"/>
                          </constantatomformula>
                        </lambdasubstitution> ) with XMLSetTermParser ).getSetTerm() must beEqualTo(
        Abs(
          Var( "x", Ti ),
          Abs(
            Var( "y", Ti ),
            HOLAtom( Const( "R", Ti -> ( Ti -> To ) ), Var( "x", Ti ) :: Var( "y", Ti ) :: Nil )
          )
        )
      )
    }
    "parse correctly a defined set \\cap(X, Y)" in {
      ( new NodeReader( <definedset symbol="\cap" definition="\cap">
                          <secondordervariable symbol="X"/>
                          <secondordervariable symbol="Y"/>
                        </definedset> ) with XMLSetTermParser ).getSetTerm() must beEqualTo(
        HOLFunction(
          Const(
            "\\cap",
            ( Ti -> To ) -> ( ( Ti -> To ) -> ( Ti -> To ) )
          ),
          Var( "X", Ti -> To ) ::
            Var( "Y", Ti -> To ) :: Nil
        )
      )
    }
    "parse correctly a defined set formula \\cup(X,Y)(c)" in {
      ( new NodeReader( <definedsetformula>
                          <definedset symbol="\cup" definition="\cup">
                            <secondordervariable symbol="X"/>
                            <secondordervariable symbol="Y"/>
                          </definedset>
                          <constant symbol="c"/>
                        </definedsetformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        App(
          HOLFunction(
            Const(
              "\\cup",
              ( Ti -> To ) -> ( ( Ti -> To ) -> ( Ti -> To ) )
            ),
            Var( "X", Ti -> To ) ::
              Var( "Y", Ti -> To ) :: Nil
          ),
          Const( "c", Ti )
        )
      )
    }
    "parse correctly a complex sentence (all X)(all Y)(all z) X(z) impl \\cup(X,Y)(z)" in {
      ( new NodeReader( <secondorderquantifiedformula type="all">
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
                        </secondorderquantifiedformula> ) with XMLFormulaParser ).getFormula() must beEqualTo(
        All(
          Var( "X", Ti -> To ),
          All(
            Var( "Y", Ti -> To ),
            All(
              Var( "z", Ti ),
              Imp(
                HOLAtom( Var( "X", Ti -> To ), Var( "z", Ti ) :: Nil ),
                ( App(
                  HOLFunction(
                    Const(
                      "\\cup",
                      ( Ti -> To ) -> ( ( Ti -> To ) -> ( Ti -> To ) )
                    ),
                    Var( "X", Ti -> To ) ::
                      Var( "Y", Ti -> To ) :: Nil
                  ),
                  Var( "z", Ti )
                ) ).asInstanceOf[HOLFormula]
              )
            )
          ) //TODO: cast should not be neccessary
        )
      )
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
      ( new NodeReader( <proof symbol="p" calculus="LK">
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
                        </proof> ) with XMLProofParser ).getProof() must
        beLike {
          case Axiom( conc ) if conc.syntacticMultisetEquals( OccSequent(
            pc( "P" ) :: Nil,
            pc( "P" ) :: Nil
          ) ) => ok
        }
    }
    "parse a permutation parameter (1 2)" in {
      XMLUtils.permStringToCycles( "(1 2)", 2 ) must
        beDeeplyEqual( ( 2 :: 1 :: Nil ).map( i => i - 1 ).toArray )
    }
    "parse a permutation parameter (1 2 3)(5 6)" in {
      XMLUtils.permStringToCycles( "(1 2 3)(5 6)", 6 ) must
        beDeeplyEqual( ( 3 :: 1 :: 2 :: 4 :: 6 :: 5 :: Nil ).map( i => i - 1 ).toArray )
    }
    "parse a permutation parameter (3 4 5) of size 5" in {
      XMLUtils.permStringToCycles( "(3 4 5)", 5 ) must
        beDeeplyEqual( ( 1 :: 2 :: 5 :: 3 :: 4 :: Nil ).map( i => i - 1 ).toArray )
    }
    "parse a permutation rule" in {
      ( new NodeReader( <rule type="permr" param="(1 3)(2)">
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
                        </rule> ) with XMLProofParser ).getProof() must
        beLike { case Axiom( conc ) => ok }
    }
    "parse a simple contraction rule" in {
      ( ( new NodeReader( <rule type="contrl" param="2">
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
                          </rule> ) with XMLProofParser ).getProof().root ) must beSyntacticMultisetEqual(
        OccSequent( pc( "A" ) :: Nil, Nil )
      )
    }
    "parse an involved contraction rule" in {
      ( new NodeReader( <rule type="contrl" param="2,1,2,1,1">
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
                        </rule> ) with XMLProofParser ).getProof().root must beSyntacticMultisetEqual(
        OccSequent( pc( "A" ) :: pc( "B" ) :: pc( "C" ) :: pc( "C" ) :: pc( "D" ) :: Nil, Nil )
      )
    }
    "parse correctly a proof of A, A :- A and A" in {
      ( new NodeReader( <proof symbol="p" calculus="LK">
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
                        </proof> ) with XMLProofParser ).getProof().root must beSyntacticMultisetEqual(
        OccSequent( pc( "A" ) :: pc( "A" ) :: Nil, fo2occ( And( pcf( "A" ), pcf( "A" ) ) ) :: Nil )
      )
    }
    "parse correctly a proof with one orr1 rule and one permr rule" in {
      ( new NodeReader( <proof symbol="p" calculus="LK">
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
                        </proof> ) with XMLProofParser ).getProof().root must beSyntacticMultisetEqual(
        OccSequent( Nil, pc( "B" ) :: fo2occ( Or( pcf( "A" ), pcf( "C" ) ) ) :: Nil )
      )
    }
    "parse correctly a proof with some permutations, an andr, and an orr1 rule from a file" in {
      val proofs = ( new XMLReader( getClass.getResourceAsStream( "/xml/test3.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase().proofs

      proofs.size must beEqualTo( 1 )
      proofs.head._2.endSequent must beMultiSetEqual(
        OccSequent( Nil, pc( "A" ) :: pc( "C" ) :: pc( "F" ) ::
        fo2occ( And( pcf( "B" ), pcf( "E" ) ) ) ::
        fo2occ( Or( pcf( "D" ), pcf( "G" ) ) ) :: Nil ).toHOLSequent
      )
    }
    "parse correctly a proof with two orr1 rules and two permr rules from a file" in {
      val proofs = ( new XMLReader( getClass.getResourceAsStream( "/xml/test2.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase().proofs

      proofs.size must beEqualTo( 1 )
      proofs.head._2.endSequent must beMultiSetEqual(
        OccSequent( Nil, fo2occ( Or( pcf( "A" ), pcf( "C" ) ) ) ::
        fo2occ( Or( pcf( "B" ), pcf( "D" ) ) ) :: Nil ).toHOLSequent
      )
    }
    "parse correctly an involved proof from a file" in {
      val proofs = ( new XMLReader( getClass.getResourceAsStream( "/xml/test1.xml" ) ) with XMLProofDatabaseParser ).getProofDatabase().proofs

      val X = Var( "X", Ti -> To )
      val t = Const( "t", Ti )
      val s = Const( "s", Ti )
      val r = Const( "r", Ti )
      val f = Const( "f", Ti -> Ti )
      val x = Var( "x", Ti )
      val Rs = Const( "R", Ti -> ( Ti -> To ) )
      val f1 = All( X, And( HOLAtom( X, t :: Nil ), Neg( HOLAtom( X, s :: Nil ) ) ) )
      val f2 = And(
        Imp( HOLAtom( Rs, r :: t :: Nil ), HOLAtom( Rs, r :: App( f, t ) :: Nil ) ),
        Ex( x, And( HOLAtom( Rs, x :: s :: Nil ), Neg( HOLAtom( Rs, x :: App( f, s ) :: Nil ) ) ) )
      )

      proofs.size must beEqualTo( 1 )
      proofs.head._2.endSequent must beMultiSetEqual( OccSequent( f1 :: Nil, f2 :: Nil ).toHOLSequent )
    }

    "parse correctly a sequentlist from a gzipped file" in {
      val proofdb = ( new XMLReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "xml" + separator + "slist.xml.gz" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()

      proofdb.sequentLists.size must beEqualTo( 1 )
    }
    "parse correctly a proof with definitions from a gzipped file" in {
      val proofdb = ( new XMLReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "xml" + separator + "prime1-0.xml.gz" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()

      proofdb.Definitions.size must beEqualTo( 21 )
    }
    "validate and detect bogus XML document using local DTD" in {
      skipped( "getting timeouts --gebner, 2015-10-22" )
      val reader = XMLReaderFactory.createXMLReader()
      reader.setEntityResolver( new CatalogResolver( new CatalogManager() ) )
      reader.setFeature( "http://xml.org/sax/features/validation", true )
      reader.setErrorHandler( new DemoErrorHandler() )
      //reader.parse("target" + separator + "test-classes" + separator + "xml" + separator + "bogus.xml") must throwA[SAXParseException]
      reader.parse( getClass.getResource( "/xml/bogus.xml" ).toString ) must throwA[SAXParseException]
    }
    "validate XML document using local DTD" in {
      skipped( "getting timeouts --gebner, 2015-10-22" )
      val reader = XMLReaderFactory.createXMLReader()
      reader.setEntityResolver( new CatalogResolver( new CatalogManager() ) )
      reader.setFeature( "http://xml.org/sax/features/validation", true )
      reader.setErrorHandler( new DemoErrorHandler() )
      //reader.parse("target" + separator + "test-classes" + separator + "xml" + separator + "test1.xml") must not (throwA[SAXParseException])
      reader.parse( getClass.getResource( "/xml/test1.xml" ).toString ) must not( throwA[SAXParseException] )
    }
  }
}

case class beDeeplyEqual[T]( a: Array[T] ) extends Matcher[Array[T]]() {
  def apply[S <: Array[T]]( v: Expectable[S] ) = result( v.value.deep.equals( a.deep ), "successful deepEquals", v.value.deep.toString + " not deepEquals " + a.deep.toString, v )
}

class DemoErrorHandler extends ErrorHandler {
  override def warning( ex: SAXParseException ): Unit = {}
  override def error( ex: SAXParseException ): Unit = { println( "Error", ex ); throw ( ex ) }
  override def fatalError( ex: SAXParseException ): Unit = println( "Fatal Error", ex )
}

