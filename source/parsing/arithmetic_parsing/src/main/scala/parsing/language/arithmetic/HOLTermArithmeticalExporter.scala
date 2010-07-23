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

trait HOLTermArithmeticalExporter extends OutputExporter with at.logic.parsing.language.HOLTermExporter {
  def exportFunction(t: LambdaExpression): Unit = {require(t.isInstanceOf[HOLExpression]); t match {
    case Function(ConstantStringSymbol("+"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" + "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("-"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" - "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("*"), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" * "); exportTerm(y); getOutput.write(")")}
    case Function(ConstantStringSymbol("""/"""), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(""" / """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol("<"), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" < """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol(">"), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(ConstantStringSymbol("="), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}

    case Function(name, args, _) => {
      getOutput.write(name.toString)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")
    }
    case Atom(name, args) => {
      getOutput.write(name.toString)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")
    }
  }}
}
