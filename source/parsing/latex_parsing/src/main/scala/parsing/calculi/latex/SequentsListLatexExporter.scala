/*
 * SequentsListPDFExporter.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.calculi.latex

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.ExportingException
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.parsing.language.latex.HOLTermLatexExporter

import scala.collection.mutable.Map

trait SequentsListLatexExporter extends HOLTermLatexExporter {
  val smskip = "\n\n"
  val mdskip = "\n\n"+ """\rule[-0.1cm]{5cm}{0.01cm} \\""" + "\n\n"
  private def exportSequent(seq: Sequent) = {
    if (seq.antecedent.size > 0) exportTerm1(seq.antecedent.head)
    if (seq.antecedent.size > 1) seq.antecedent.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportTerm1(x)})
    getOutput.write(smskip); getOutput.write(""" $\vdash$ """); getOutput.write(smskip)
    if (seq.succedent.size > 0) exportTerm1(seq.succedent.head)
    if (seq.succedent.size > 1) seq.succedent.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportTerm1(x)})
  }
  
  def exportSequentList(ls: List[Sequent], sections: List[Tuple2[String,List[Tuple2[Any,Any]]]]): OutputExporter = {
    // first obtain information about the clauses, replace lambda expressions of constant type by constants (and describe it at the top of the page)
    // Also describe the types of all constants

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
    sections.foreach(x => {
      getOutput.write("""\section{""" + x._1 + "}")
      getOutput.write("\n")
      getOutput.write("""\begin{tabular}{ll}""")
      x._2.foreach(y => {
        printOnMatch(y._1)
        getOutput.write(" & ")
        printOnMatch(y._2)
        getOutput.write(""" \\ """)
        getOutput.write("\n")
      })
      getOutput.write("""\end{tabular}""")
      getOutput.write("\n")
    })
    getOutput.write("""\section{Clauses}""")
    getOutput.write("\n")
    ls.foreach(x => {exportSequent(x); getOutput.write(mdskip)})
    getOutput.write("""\end{document}""")
    this
  }

  private def printOnMatch(a: Any) = a match {
    case le: LambdaExpression => exportTerm1(le)
    case ta: TA => getOutput.write("$" + latexType(ta) + "$")
    case _ => getOutput.write(a.toString)
  }
  
  private def exportTerm1(f: LambdaExpression) = {
    getOutput.write("$")
    exportTerm(f)
    getOutput.write("$")
  }
  /*private def replaceTerm(f: LambdaExpression, defs: Map[Int, Tuple2[Abs,Var]]): LambdaExpression = f match {
    case v: Var => v
    case App(a,b) => App(replaceTerm(a, defs), replaceTerm(b, defs))
    case a @ Abs(x,b) => defs.get(extractAbs(a.asInstanceOf[Abs])) match {
      case Some(v) => v._2
      case _ => Abs(x, replaceTerm(b, defs))
    }
  }*/
}

trait LabelledSequentsListLatexExporter extends HOLTermLatexExporter {
  val smskip = "\n\n"
  val mdskip = "\n\n"+ """\rule[-0.1cm]{5cm}{0.01cm} \\""" + "\n\n"
  private def exportSequent(seq: LabelledSequentOccurrence) = {
    val ant = seq.l_antecedent.toList
    val suc = seq.l_succedent.toList
    if (ant.size > 0) exportLabelledFormulaOccurrence(ant.first)
    if (ant.size > 1) ant.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportLabelledFormulaOccurrence(x)})
    getOutput.write(smskip); getOutput.write(""" $\vdash$ """); getOutput.write(smskip)
    if (suc.size > 0) exportLabelledFormulaOccurrence(suc.first)
    if (suc.size > 1) suc.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportLabelledFormulaOccurrence(x)})
  }
  
  def exportSequentList(ls: List[LabelledSequentOccurrence], sections: List[Tuple2[String,List[Tuple2[Any,Any]]]]): OutputExporter = {
    // first obtain information about the clauses, replace lambda expressions of constant type by constants (and describe it at the top of the page)
    // Also describe the types of all constants

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
    sections.foreach(x => {
      getOutput.write("""\section{""" + x._1 + "}")
      getOutput.write("\n")
      getOutput.write("""\begin{tabular}{ll}""")
      x._2.foreach(y => {
        printOnMatch(y._1)
        getOutput.write(" & ")
        printOnMatch(y._2)
        getOutput.write(""" \\ """)
        getOutput.write("\n")
      })
      getOutput.write("""\end{tabular}""")
      getOutput.write("\n")
    })
    getOutput.write("""\section{Clauses}""")
    getOutput.write("\n")
    ls.foreach(x => {exportSequent(x); getOutput.write(mdskip)})
    getOutput.write("""\end{document}""")
    this
  }

  private def printOnMatch(a: Any) = a match {
    case le: LambdaExpression => exportTerm1(le)
    case fo: LabelledFormulaOccurrence => exportLabelledFormulaOccurrence(fo)
    case ta: TA => getOutput.write("$" + latexType(ta) + "$")
    case _ => getOutput.write(a.toString)
  }
  
  private def exportTerm1(f: LambdaExpression) = {
    getOutput.write("$")
    exportTerm(f)
    getOutput.write("$")
  }

  private def exportLabelledFormulaOccurrence( fo: LabelledFormulaOccurrence ) = {
    getOutput.write("""$\left<""")
    exportTerm(fo.formula)
    getOutput.write("""\right>^{""")
    fo.label.foreach( t => {
      exportTerm( t )
      getOutput.write(", ")
    } )
    getOutput.write("""}$""")
  }
  /*private def replaceTerm(f: LambdaExpression, defs: Map[Int, Tuple2[Abs,Var]]): LambdaExpression = f match {
    case v: Var => v
    case App(a,b) => App(replaceTerm(a, defs), replaceTerm(b, defs))
    case a @ Abs(x,b) => defs.get(extractAbs(a.asInstanceOf[Abs])) match {
      case Some(v) => v._2
      case _ => Abs(x, replaceTerm(b, defs))
    }
  }*/
}
