/*
 * HOLTermExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.xml

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.ExportingException

trait HOLTermExporter {
  def exportTerm(term: HOLTerm): scala.xml.Elem = term match {
    case Atom(ConstantStringSymbol(name),args) =>
      <constantatomformula symbol={name}>
        {exportList(args)}
      </constantatomformula>
    case AppN1(func@Var(VariableStringSymbol(_), FunctionType(To(),_)),args) =>
      <variableatomformula>
        {exportList(func::args)}
      </variableatomformula>
    case And(left,right) =>
      <conjunctiveformula type="and">
        {exportList(left::right::Nil)}
      </conjunctiveformula>
    case Or(left,right) =>
      <conjunctiveformula type="or">
        {exportList(left::right::Nil)}
      </conjunctiveformula>
    case Imp(left,right) =>
      <conjunctiveformula type="impl">
        {exportList(left::right::Nil)}
      </conjunctiveformula>
    case Neg(f) =>
      <conjunctiveformula type="neg">
        {exportTerm(f)}
      </conjunctiveformula>
    case _ => exportTerm2(term)
  }
  private def exportTerm2(term: HOLTerm): scala.xml.Elem = term match {
    case AllVar(vr@Var(_,Ti()),f) =>
      <quantifiedformula type="all">
        {exportList(vr::f::Nil)}
      </quantifiedformula>
    case ExVar(vr@Var(_,Ti()),f) =>
      <quantifiedformula type="exists">
        {exportList(vr::f::Nil)}
      </quantifiedformula>
    case AllVar(vr@Var(_,->(Ti(),To())),f) =>
      <secondorderquantifiedformula type="all">
        {exportList(vr::f::Nil)}
      </secondorderquantifiedformula>
    case ExVar(vr@Var(_,->(Ti(),To())),f) =>
      <secondorderquantifiedformula type="exists">
        {exportList(vr::f::Nil)}
      </secondorderquantifiedformula>
    case _ => exportTerm3(term)
  }
  private def exportTerm3(term: HOLTerm): scala.xml.Elem = term match {
    case Var(VariableStringSymbol(a), Ti()) =>
      <variable symbol={a}/>
    case Var(ConstantStringSymbol(a), Ti()) =>
      <constant symbol={a}/>
    case AppN1(Var(ConstantStringSymbol(a),FunctionType(Ti(),_)),args) =>
      <function symbol={a}>
        {exportList(args)}
      </function>
    case Var(VariableStringSymbol(a), ->(Ti(),To())) =>
      <secondordervariable symbol={a}/>
    case AbsN1(varlist, func) =>
      <lambdasubstitution>
        <variablelist>
          {exportList(varlist)}
        </variablelist>{exportTerm(func.asInstanceOf[HOLTerm])}
      </lambdasubstitution>
    case AppN(Var(ConstantStringSymbol(a),FunctionType(To(),ls)),args) if (ls.last == Ti()) =>
      <definedset definition={a} symbol={a}>
        {exportList(args)}
      </definedset>
    case _ => throw new ExportingException("Term cannot be exported into the required xml format: " + term.toString)
  }
  private def exportList(ls: List[LambdaExpression]) = ls.map(x => exportTerm(x.asInstanceOf[HOLTerm]))
}