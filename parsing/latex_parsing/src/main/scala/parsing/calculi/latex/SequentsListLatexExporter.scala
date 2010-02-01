/*
 * SequentsListPDFExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi.latex

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
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.parsing.language.latex.HOLTermLatexExporter

trait SequentsListLatexExporter extends HOLTermLatexExporter {
  private def exportSequent(seq: Sequent) = {
    getOutput.write("$")
    if (seq.antecedent.size > 0) exportTerm(seq.antecedent.head)
    if (seq.antecedent.size > 1) seq.antecedent.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
    getOutput.write("""\vdash""")
    if (seq.succedent.size > 0) exportTerm(seq.succedent.head)
    if (seq.succedent.size > 1) seq.succedent.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
    getOutput.write("$")
  }
  
  def exportSequentList(ls: List[Sequent]): OutputExporter = {
    getOutput.write("""\documentclass[10pt, a4paper]{article}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\topmargin}{-1.5cm}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\headheight}{0cm}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\headsep}{0cm}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\textheight}{1.25\textheight}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\oddsidemargin}{-1.5cm}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\evensidemargin}{-1.5cm}""")
    getOutput.write("\n")
    getOutput.write("""\setlength{\textwidth}{1.4\textwidth}""")
    getOutput.write("\n")
    getOutput.write("""\begin{document}""")
    getOutput.write("\n")
    getOutput.write("""\tiny""")
    getOutput.write("\n")
    ls.foreach(x => {exportSequent(x); getOutput.write("\n\n")})
    getOutput.write("""\end{document}""")
    this
  }
    
}
