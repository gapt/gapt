/*
 * HOLExpressionExporterTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.xml

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
import at.logic.parsing.language.xml._
import scala.xml.Utility.trim

class HOLTermExporterTest extends SpecificationWithJUnit {
  
  val exporter = new HOLTermExporter{}
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = HOLConstFormula( new ConstantStringSymbol( sym ) )
  
  "HOLExpressionExporter" should {
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
    