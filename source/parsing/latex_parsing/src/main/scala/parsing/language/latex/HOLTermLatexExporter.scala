/*
 * HOLTermLatexExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.latex

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.quantifiers._
import at.logic.parsing.OutputExporter
import at.logic.language.lambda.typedLambdaCalculus._

trait HOLTermLatexExporter extends OutputExporter with HOLTermExporter {
  // it is LambdaExpression and require because of the stupid design chose not to have a common element for HOL
  def exportTerm(t: LambdaExpression): Unit = {require(t.isInstanceOf[HOLTerm]); t match {
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
}
