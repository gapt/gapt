/*
 * SequentsListPDFExporter.scala
 *
 */

package at.logic.parsing.calculi.latex

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.parsing.ExportingException
import at.logic.parsing.OutputExporter
import at.logic.parsing.language.latex.HOLTermLatexExporter


trait SequentsListLatexExporter extends HOLTermLatexExporter {
  val smskip = "\n\n"
  val mdskip = "\n\n"+ """\rule[-0.1cm]{5cm}{0.01cm} \\""" + "\n\n"
  private def exportSequent(seq: FSequent) = {
    if (seq._1.size > 0) exportTerm1(seq._1.head)
    if (seq._1.size > 1) seq._1.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportTerm1(x)})
    getOutput.write(smskip); getOutput.write(""" $\vdash$ """); getOutput.write(smskip)
    if (seq._2.size > 0) exportTerm1(seq._2.head)
    if (seq._2.size > 1) seq._2.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportTerm1(x)})
  }
  
  def exportSequentList(ls: List[FSequent], sections: List[Tuple2[String,List[Tuple2[Any,Any]]]]): OutputExporter = {
    // first obtain information about the clauses, replace lambda expressions of constant type by constants (and describe it at the top of the page)
    // Also describe the types of all constants

    getOutput.write("""\documentclass[10pt, a4paper]{article}""")
    getOutput.write("\n")
    getOutput.write("""\""")
    getOutput.write("""usepackage{color}""")
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
    printTypes(ls)
    getOutput.write("""\end{document}""")
    this
  }

  private def getFSVars(fs:FSequent) : Set[HOLVar] = fs.formulas.toSet.flatMap(getVars)
  private def getVars(l: HOLExpression) : Set[HOLVar] = l match {
    case v: HOLVar => Set(v)
    case c: HOLConst => Set()
    case HOLAbs(x,t) => getVars(t) ++ getVars(x)
    case HOLApp(s,t) => getVars(s) ++ getVars(t)
  }

  private def getFSConsts(fs:FSequent) : Set[HOLConst] = fs.formulas.toSet.flatMap(getConsts)
  private def getConsts(l: HOLExpression) : Set[HOLConst] = l match {
    case v: HOLVar => Set()
    case c: HOLConst => Set(c)
    case HOLAbs(x,t) => getConsts(t) ++ getConsts(x)
    case HOLApp(s,t) => getConsts(s) ++ getConsts(t)
  }

  def printTypes(l: List[FSequent]) = {
    val (vmap, cmap) = getTypes(l)
    getOutput.write("\\subsection{Variable Types}\n")

    getOutput.write("\\[\\begin{array}{ll}\n")
    for ((key,set) <- vmap.toList.sortBy(_._1)(TAOrdering)) {
      var set_ = set.toList.sorted
      while (set_.nonEmpty) {
        val (ten,rest) = set_.splitAt(10)
        getOutput.write(ten.mkString("",", "," & ")+typeToString(key))
        getOutput.write(" \\\\\n")
        set_ = rest
      }
    }
    getOutput.write("""\end{array}\]""")

    getOutput.write("\\subsection{Constant Types}\n")
    getOutput.write("\\[\\begin{array}{ll}\n")
    for ((key,set) <- cmap.toList.sortBy(_._1)(TAOrdering)) {
      var set_ = set.toList.sorted
      while (set_.nonEmpty) {
        val (ten,rest) = set_.splitAt(10)
        getOutput.write(ten.mkString("",", "," & ")+typeToString(key))
        getOutput.write(" \\\\\n")
        set_ = rest
      }
    }
    getOutput.write("""\end{array}\]""")
  }

  def typeToString(t:TA, outermost : Boolean = true) : String = t match {
    case Ti => "i"
    case To => "o"
    case Tindex => "w"
    case t1 -> t2 =>
      typeToString_(t1) +
      " > " +
      typeToString_(t2)
  }

  def typeToString_(t:TA) : String = t match {
    case Ti => "i"
    case To => "o"
    case Tindex => "w"
    case t1 -> t2 =>
      ("(") +
        typeToString_(t1) +
        " > " +
        typeToString_(t2) +
      ")"
  }

  private def getTypes(l:List[FSequent]) = {
    val vars = l.foldLeft(Set[HOLVar]()) ((acc, fs) => acc ++ getFSVars(fs))
    val consts = l.foldLeft(Set[HOLConst]()) ((acc, fs) => acc ++ getFSConsts(fs))
    val svars = vars.map(_.name.toString())
    val cvars = consts.map(_.name.toString())
    if (cvars.exists(svars.contains(_)) || svars.exists(cvars.contains(_)))
      println("WARNING: exported const and varset are not disjunct!")

    val varmap = vars.foldLeft(Map[TA,Set[String]]())((map, v) => {
      if (map contains v.exptype) {
        val nset =  map(v.exptype) + v.name.toString()
        map + ((v.exptype, nset))
      } else {
        map + ((v.exptype, Set(v.name.toString())))
      }
    })
    val constmap = consts.foldLeft(Map[TA,Set[String]]())((map, v) => {
      if (map contains v.exptype) {
        val nset =  map(v.exptype) + v.name.toString()
        map + ((v.exptype, nset))
      } else {
        map + ((v.exptype, Set(v.name.toString())))
      }
    })

    (varmap,constmap)
  }

  private def printOnMatch(a: Any) = a match {
    case le: HOLExpression => exportTerm1(le)
    case ta: TA => getOutput.write("$" + latexType(ta) + "$")
    case _ => getOutput.write(a.toString)
  }


  private def exportTerm1(f: HOLExpression) = {
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
  private def exportSequent(seq: LabelledSequent) = {
    val ant = seq.l_antecedent.toList
    val suc = seq.l_succedent.toList
    if (ant.size > 0) exportLabelledFormulaOccurrence(ant.head)
    if (ant.size > 1) ant.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportLabelledFormulaOccurrence(x)})
    getOutput.write(smskip); getOutput.write(""" $\vdash$ """); getOutput.write(smskip)
    if (suc.size > 0) exportLabelledFormulaOccurrence(suc.head)
    if (suc.size > 1) suc.tail.foreach(x => {getOutput.write(smskip); /*getOutput.write(",");*/ exportLabelledFormulaOccurrence(x)})
  }
  
  def exportSequentList(ls: List[LabelledSequent], sections: List[Tuple2[String,List[Tuple2[Any,Any]]]]): at.logic.parsing.OutputExporter = {
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
    case le: HOLExpression => exportTerm1(le)
    case fo: LabelledFormulaOccurrence => exportLabelledFormulaOccurrence(fo)
    case ta: TA => getOutput.write("$" + latexType(ta) + "$")
    case _ => getOutput.write(a.toString)
  }
  
  private def exportTerm1(f: HOLExpression) = {
    getOutput.write("$")
    exportTerm(f)
    getOutput.write("$")
  }

  private def exportLabelledFormulaOccurrence( fo: LabelledFormulaOccurrence ) = {
    getOutput.write("""$\left<""")
    exportTerm(fo.formula)
    getOutput.write("""\right>^{""")
    fo.skolem_label.foreach( t => {
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

