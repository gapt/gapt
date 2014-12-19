/*
 * HOLExpressionExporterTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.xml

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import scala.xml._

import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator
import at.logic.parsing.language.xml._
import scala.xml.Utility.trim
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.StringSymbol

@RunWith(classOf[JUnitRunner])
class HOLTermExporterTest extends SpecificationWithJUnit {
  
  val exporter = new HOLTermExporter{}
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = Atom( HOLConst( sym, To ) )
  
  "HOLExpressionExporter" should {
    "export correctly a constant c" in {
      exporter.exportTerm(HOLConst("c", "i")) must beEqualTo(<constant symbol="c"/>)
    }
    "export correctly a term g(c)" in {
      trim(exporter.exportTerm(HOLApp(HOLConst("g",Ti -> Ti), HOLConst("c", "i")))) must beEqualTo(<function symbol="g"><constant symbol="c"/></function>)
    }
    "export correctly a variable x" in {
      trim(exporter.exportTerm(HOLVar("x", Ti))) must beEqualTo (<variable symbol="x"></variable>)
    }
    "export correctly a term f(x,c)" in {
      trim(exporter.exportTerm(
        Function(HOLConst("f", Ti -> (Ti -> Ti)),
          List(HOLVar(StringSymbol("x"), Ti), HOLConst("c", Ti))))) must beEqualTo (
        <function symbol="f"><variable symbol="x"/><constant symbol="c"/></function>
      )
    }
    "export correctly an atom formula P(f(x,c),y)" in {
      trim(exporter.exportTerm(Atom(HOLConst("P",Ti -> (Ti -> To)), List(
        Function(HOLConst("f", Ti -> (Ti -> Ti)),
          List(HOLVar("x", Ti), HOLConst("c", Ti))),
        HOLVar("y", Ti))))) must beEqualTo (trim(
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
      trim(exporter.exportTerm(And(pc("P"), pc("Q")))) must beEqualTo (trim(
        <conjunctiveformula type="and">
         <constantatomformula symbol="P"/>
         <constantatomformula symbol="Q"/>
        </conjunctiveformula>
      ))
    }
    "export correctly a quantified formula (exists x) x = x" in {
      trim(exporter.exportTerm(ExVar(HOLVar("x", Ti), Equation(HOLVar("x", Ti), HOLVar("x", Ti))))) must beEqualTo (trim(
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
      trim(exporter.exportTerm(HOLVar("X", Ti -> To))) must beEqualTo (trim(
        <secondordervariable symbol="X"/>
      ))
    }
    "export correctly a variable atom formula X(c)" in {
      trim(exporter.exportTerm(Atom(HOLVar("X",Ti -> To), HOLConst("c", Ti)::Nil))) must beEqualTo (trim(
        <variableatomformula>
          <secondordervariable symbol="X"/>
          <constant symbol="c"/>
        </variableatomformula>
      ))
    }
    "export correctly a second-order quantified formula (all Z)Z(c)" in {
      trim(exporter.exportTerm(AllVar(HOLVar("Z", Ti -> To), Atom(HOLVar("Z", Ti -> To), HOLConst("c", "i")::Nil)))) must beEqualTo (trim(
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
      trim(exporter.exportTerm(HOLAbs(HOLVar("x", Ti), Atom(HOLConst("P", Ti -> To), HOLVar("x", Ti)::Nil)))) must beEqualTo (trim(
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
      trim(exporter.exportTerm(HOLAbs(HOLVar("x", Ti), HOLAbs(HOLVar("y", Ti),
        Atom(HOLConst("R", Ti -> (Ti -> To)), List(HOLVar("x", Ti), HOLVar("y", Ti))))))) must beEqualTo (trim(
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
      trim(exporter.exportTerm(HOLApp(
        HOLApp(HOLConst( "\\cap",(Ti -> To) -> ((Ti -> To) -> (Ti -> To))),
               HOLVar("X", Ti -> To )),
        HOLVar( "Y", Ti -> To )))) must beEqualTo (trim(
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
          HOLConst( new ConstantStringSymbol("c"), "i" ) ))) must beEqualTo (trim(
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
                    HOLVar( "z", "i" ) ) ) ) ) ) )) must beEqualTo (trim(
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
    