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
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.ExportingException
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.parsing.language.latex.HOLTermLatexExporter

import scala.collection.mutable.Map

trait SequentsListLatexExporter extends HOLTermLatexExporter {
  val smskip = "\n\n"
  val mdskip = "\n\n"+ """\rule[-0.1cm]{5cm}{0.01cm} \\""" + "\n\n"
  private def exportSequent(seq: Sequent, defs: Map[Int, Tuple2[Abs,Var]]) = {
    if (seq.antecedent.size > 0) exportTerm1(seq.antecedent.head,defs)
    if (seq.antecedent.size > 1) seq.antecedent.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportTerm1(x,defs)})
    getOutput.write(smskip); getOutput.write(""" $\vdash$ """); getOutput.write(smskip)
    if (seq.succedent.size > 0) exportTerm1(seq.succedent.head,defs)
    if (seq.succedent.size > 1) seq.succedent.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportTerm1(x,defs)})
  }
  
  def exportSequentList(ls: List[Sequent]): OutputExporter = {
    // first obtain information about the clauses, replace lambda expressions of constant type by constants (and describe it at the top of the page)
    // Also describe the types of all constants

    val types = Map[LambdaExpression, String]()
    val defs = Map[Int, Tuple2[Abs,Var]]()
    ls.foreach(x => mapValues(x, types, defs))
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
    getOutput.write("""\section{Types}""")
    getOutput.write("\n")
    getOutput.write("""\begin{tabular}{ll}""")
    types.toList.sort((x,y) => x._1.toString < y._1.toString).foreach(x => {exportTerm1(x._1,defs); getOutput.write(" & "); getOutput.write(x._2); getOutput.write(""" \\ """); getOutput.write("\n")})
    getOutput.write("""\end{tabular}""")
    getOutput.write("\n")
    getOutput.write("""\section{Definitions}""")
    getOutput.write("\n")
    getOutput.write("""\begin{tabular}{ll}""")
    val dumap = Map[Int, Tuple2[Abs,Var]]()
    defs.foreach(x => {exportTerm1(x._2._2,dumap); getOutput.write(" & "); exportTerm1(x._2._1,dumap); getOutput.write(""" \\ """); getOutput.write("\n")})
    getOutput.write("""\end{tabular}""")
    getOutput.write("\n")
    getOutput.write("""\section{Clauses}""")
    getOutput.write("\n")
    ls.foreach(x => {exportSequent(x, defs); getOutput.write(mdskip)})
    getOutput.write("""\end{document}""")
    this
  }
  object DefId {
   var id = 0
   def nextId = {id = id + 1; id}
  }
  private def mapValues(s: Sequent, types: Map[LambdaExpression, String], defs: Map[Int, Tuple2[Abs,Var]]) = {s.antecedent.foreach(mapValuesInTerm(types,defs));  s.succedent.foreach(mapValuesInTerm(types,defs));}
  private def mapValuesInTerm(types: Map[LambdaExpression, String], defs: Map[Int, Tuple2[Abs,Var]])(f: LambdaExpression): Unit = f match {
    case v @ Var(at.logic.language.hol.logicSymbols.ConstantStringSymbol(x), t) => types.getOrElseUpdate(v, "$" + latexType(t) + "$")
    case App(a,b) => mapValuesInTerm(types,defs)(a); mapValuesInTerm(types,defs)(b)
    case a @ Abs(x,b) => {
      mapValuesInTerm(types,defs)(b)
      defs.get(extractAbs(a.asInstanceOf[Abs])) match {
        case Some(_) => ()
        case None => {
          val newConst: Var = x.factory.createVar(at.logic.language.hol.logicSymbols.ConstantStringSymbol("q_{" + DefId.nextId + "}"), a.exptype)
          defs.put(extractAbs(a.asInstanceOf[Abs]), (a.asInstanceOf[Abs], newConst))
          types.getOrElseUpdate(newConst, "$" + latexType(newConst.exptype) + "$")
        }
      }
    }
    case _ => ()
  }
  // ignore variants
  private def extractAbs(a: Abs): Int = a.hashCode
  
  private def exportTerm1(f: LambdaExpression, defs: Map[Int, Tuple2[Abs,Var]]) = {
    getOutput.write("$")
    exportTerm(replaceTerm(f, defs))
    getOutput.write("$")
  }
  private def replaceTerm(f: LambdaExpression, defs: Map[Int, Tuple2[Abs,Var]]): LambdaExpression = f match {
    case v: Var => v
    case App(a,b) => App(replaceTerm(a, defs), replaceTerm(b, defs))
    case a @ Abs(x,b) => defs.get(extractAbs(a.asInstanceOf[Abs])) match {
      case Some(v) => v._2
      case _ => Abs(x, replaceTerm(b, defs))
    }
  }
  private def latexType(ta: TA): String = ta match {
    case Ti() => "i"
    case To() => "o"
    case ->(a,b) => "(" + latexType(a) + """ \rightarrow """ + latexType(b) + ")"
  }
}
