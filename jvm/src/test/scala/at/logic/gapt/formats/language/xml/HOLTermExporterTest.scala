/*
 * LambdaExpressionExporterTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.expr.xml

import at.logic.gapt.formats.xml.HOLTermXMLExporter
import org.specs2.mutable._

import scala.xml._

import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base._
import java.util.zip.GZIPInputStream
import java.io.{ FileReader, FileInputStream, InputStreamReader }
import java.io.File.separator
import scala.xml.Utility.trim
import at.logic.gapt.expr._

class HOLTermExporterTest extends Specification {

  val exporter = new HOLTermXMLExporter {}
  // helper to create 0-ary predicate constants
  def pc( sym: String ) = HOLAtom( Const( sym, To ) )

  "LambdaExpressionExporter" should {
    "export correctly a constant c" in {
      exporter.exportTerm( Const( "c", Ti ) ) must beEqualTo( <constant symbol="c"/> )
    }
    "export correctly a term g(c)" in {
      trim( exporter.exportTerm( App( Const( "g", Ti -> Ti ), Const( "c", Ti ) ) ) ) must beEqualTo( <function symbol="g"><constant symbol="c"/></function> )
    }
    "export correctly a variable x" in {
      trim( exporter.exportTerm( Var( "x", Ti ) ) ) must beEqualTo( <variable symbol="x"></variable> )
    }
    "export correctly a term f(x,c)" in {
      trim( exporter.exportTerm(
        HOLFunction(
          Const( "f", Ti -> ( Ti -> Ti ) ),
          List( Var( StringSymbol( "x" ), Ti ), Const( "c", Ti ) )
        )
      ) ) must beEqualTo(
        <function symbol="f"><variable symbol="x"/><constant symbol="c"/></function>
      )
    }
    "export correctly an atom formula P(f(x,c),y)" in {
      trim( exporter.exportTerm( HOLAtom( Const( "P", Ti -> ( Ti -> To ) ), List(
        HOLFunction(
          Const( "f", Ti -> ( Ti -> Ti ) ),
          List( Var( "x", Ti ), Const( "c", Ti ) )
        ),
        Var( "y", Ti )
      ) ) ) ) must beEqualTo( trim(
        <constantatomformula symbol="P">
          <function symbol="f">
            <variable symbol="x"/>
            <constant symbol="c"/>
          </function>
          <variable symbol="y"/>
        </constantatomformula>
      ) )
    }
    "export correctly a conjunction of atoms P and Q" in {
      trim( exporter.exportTerm( And( pc( "P" ), pc( "Q" ) ) ) ) must beEqualTo( trim(
        <conjunctiveformula type="and">
          <constantatomformula symbol="P"/>
          <constantatomformula symbol="Q"/>
        </conjunctiveformula>
      ) )
    }
    "export correctly a quantified formula (exists x) x = x" in {
      trim( exporter.exportTerm( Ex( Var( "x", Ti ), Eq( Var( "x", Ti ), Var( "x", Ti ) ) ) ) ) must beEqualTo( trim(
        <quantifiedformula type="exists">
          <variable symbol="x"/>
          <constantatomformula symbol="=">
            <variable symbol="x"/>
            <variable symbol="x"/>
          </constantatomformula>
        </quantifiedformula>
      ) )
    }
    "export correctly a second-order variable X" in {
      trim( exporter.exportTerm( Var( "X", Ti -> To ) ) ) must beEqualTo( trim(
        <secondordervariable symbol="X"/>
      ) )
    }
    "export correctly a variable atom formula X(c)" in {
      trim( exporter.exportTerm( HOLAtom( Var( "X", Ti -> To ), Const( "c", Ti ) :: Nil ) ) ) must beEqualTo( trim(
        <variableatomformula>
          <secondordervariable symbol="X"/>
          <constant symbol="c"/>
        </variableatomformula>
      ) )
    }
    "export correctly a second-order quantified formula (all Z)Z(c)" in {
      trim( exporter.exportTerm( All( Var( "Z", Ti -> To ), HOLAtom( Var( "Z", Ti -> To ), Const( "c", Ti ) :: Nil ) ) ) ) must beEqualTo( trim(
        <secondorderquantifiedformula type="all">
          <secondordervariable symbol="Z"/>
          <variableatomformula>
            <secondordervariable symbol="Z"/>
            <constant symbol="c"/>
          </variableatomformula>
        </secondorderquantifiedformula>
      ) )
    }
    "export correctly a LambdaExpression lambda x . P(x)" in {
      trim( exporter.exportTerm( Abs( Var( "x", Ti ), HOLAtom( Const( "P", Ti -> To ), Var( "x", Ti ) :: Nil ) ) ) ) must beEqualTo( trim(
        <lambdasubstitution>
          <variablelist>
            <variable symbol="x"/>
          </variablelist>
          <constantatomformula symbol="P">
            <variable symbol="x"/>
          </constantatomformula>
        </lambdasubstitution>
      ) )
    }
    "export correctly a LambdaExpression lambda x,y. R(x,y)" in {
      trim( exporter.exportTerm( Abs( Var( "x", Ti ), Abs(
        Var( "y", Ti ),
        HOLAtom( Const( "R", Ti -> ( Ti -> To ) ), List( Var( "x", Ti ), Var( "y", Ti ) ) )
      ) ) ) ) must beEqualTo( trim(
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
      ) )
    }
    "export correctly a defined set \\cap(X, Y)" in {
      trim( exporter.exportTerm( App(
        App(
          Const( "\\cap", ( Ti -> To ) -> ( ( Ti -> To ) -> ( Ti -> To ) ) ),
          Var( "X", Ti -> To )
        ),
        Var( "Y", Ti -> To )
      ) ) ) must beEqualTo( trim(
        <definedset symbol="\cap" definition="\cap">
          <secondordervariable symbol="X"/>
          <secondordervariable symbol="Y"/>
        </definedset>
      ) )
    }
    // definedsetformula is not supported yet
    /*"export correctly a defined set formula \\cup(X,Y)(c)" in {
      trim(exporter.exportTerm(App(AppN( Const( new ConstantStringSymbol("\\cup"), "((i -> o) -> ((i -> o) -> (i -> o)))"),
          Var( new VariableStringSymbol("X"), "(i -> o)" )::Var( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
          Const( new ConstantStringSymbol("c"), "i" ) ))) must beEqualTo (trim(
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
      trim(exporter.exportTerm(All( Var( new VariableStringSymbol("X"), "(i -> o)" ),
          All( Var( new VariableStringSymbol("Y"), "(i -> o)"),
            All( Var( new VariableStringSymbol("z"), "i"),
              Imp( Atom( new VariableStringSymbol("X"), Var( "z", "i" )::Nil ),
                AppFormula(AppN( Const( new ConstantStringSymbol("\\cup"),
                                   "((i -> o) -> ((i -> o) -> (i -> o)))"),
                           Var( new VariableStringSymbol("X"), "(i -> o)" )::
                           Var( new VariableStringSymbol("Y"), "(i -> o)" )::Nil),
                    Var( "z", "i" ) ) ) ) ) ) )) must beEqualTo (trim(
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
