/*
 * HOLExpressionLatexExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.latex

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol._
import at.logic.parsing.OutputExporter
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.schema.indexedOmegaVar

trait HOLTermLatexExporter extends OutputExporter with at.logic.parsing.language.HOLTermExporter {
  // it is LambdaExpression and require because of the stupid design chose not to have a common element for HOL
  def exportTerm(t: LambdaExpression): Unit = {require(t.isInstanceOf[HOLExpression]); t match {
    case indv: indexedOmegaVar => getOutput.write(indv.name.toString + """_{""" + indv.index+"""}""")
    case Var(name, _) => getOutput.write(name.toString)
    case Neg(f) => {getOutput.write("("); getOutput.write("""\neg """); exportTerm(f); getOutput.write(")")}
    case And(f1,f2) => {getOutput.write("("); exportTerm(f1); getOutput.write(""" \wedge """); exportTerm(f2); getOutput.write(")")}
    case Or(f1,f2) => {getOutput.write("("); exportTerm(f1); getOutput.write(""" \vee """); exportTerm(f2); getOutput.write(")")}
    case Imp(f1,f2) => {getOutput.write("("); exportTerm(f1); getOutput.write(""" \rightarrow """); exportTerm(f2); getOutput.write(")")}
    case ExVar(v, f) => {getOutput.write("("); getOutput.write("""\exists """); exportTerm(v); getOutput.write("""."""); exportTerm(f); getOutput.write(")")}
    case AllVar(v, f) => {getOutput.write("("); getOutput.write("""\forall """); exportTerm(v); getOutput.write("""."""); exportTerm(f); getOutput.write(")")}
    case Abs(v, t) => {getOutput.write("("); getOutput.write("""\lambda """); exportTerm(v); getOutput.write("""."""); exportTerm(t); getOutput.write(")")}
    case Atom(name, args) => exportFunction(t)
    case Function(name, args, _) => exportFunction(t)
  }}

  protected def latexType(ta: TA): String = ta match {
    case Ti() => "i"
    case To() => "o"
    case ->(a,b) => "(" + latexType(a) + """ \rightarrow """ + latexType(b) + ")"
  }
}
