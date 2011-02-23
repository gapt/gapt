/*
 * HOLExpressionArithmeticalExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.arithmetic

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol._
import at.logic.parsing.OutputExporter
import at.logic.language.lambda.typedLambdaCalculus._

// for schemas
import at.logic.language.schema.{BiggerThanSymbol, TopC, BottomC, BigAnd, SchemaFormula}

// FIXME: bad import, we don't want to import
// something from transformations here.
import at.logic.transformations.ceres.struct.ClauseSetSymbol
import at.logic.transformations.ceres.struct.TypeSynonyms.CutConfiguration


trait HOLTermArithmeticalExporter extends OutputExporter with at.logic.parsing.language.HOLTermExporter {
  def exportFunction(t: LambdaExpression): Unit = {require(t.isInstanceOf[HOLExpression]); t match {
    case TopC => getOutput.write("\\top")
    case BottomC => getOutput.write("\\bot")
    case Function(ConstantStringSymbol("+"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" + "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("-"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" - "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("*"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" * "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("""/"""), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(""" / """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol("<"), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" < """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol(">"), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(BiggerThanSymbol, x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol("="), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}
    case BigAnd(v, f, s, e) => {
      getOutput.write("("); getOutput.write("""\bigwedge_{"""); exportTerm(v); 
                                getOutput.write(" = "); exportTerm(s) ; getOutput.write("}^{"); exportTerm(e);
                                getOutput.write("}"); exportTerm(f); getOutput.write(")")}


    case Function(name, args, _) => {
      exportSymbol(name)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")
    }
    case Atom(name, args) => {
      exportSymbol(name)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")
    }
  }}

  def exportSymbol(sym: SymbolA): Unit = sym match {
    case cs : ClauseSetSymbol => getOutput.write("CL^{("); writeCutConf(cs.cut_occs); getOutput.write("),"); getOutput.write(cs.name); getOutput.write("}")
    case _ => getOutput.write(sym.toString)
  }

  private def writeCutConf( cc: CutConfiguration) = {
    cc._1.foreach ( f => {getOutput.write(", "); exportTerm( f )} )
    getOutput.write("|")
    cc._2.foreach ( f => {getOutput.write(", "); exportTerm( f )} )
  }
}
