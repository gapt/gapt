package gapt.testing

import gapt.expr._
import gapt.proofs.expansion.InstanceTermEncoding
import gapt.proofs.loadExpansionProof

import scala.App
import os._
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.ty.Ti
import gapt.expr.util.constants
import gapt.expr.util.freeVariables

object dumpTermset extends App {
  val Array(inputFileName, outputFileName) = args
  val inputPath = Path(inputFileName, pwd)
  val outputPath = Path(outputFileName, pwd)

  def simplifyNames(termset: Set[FOLTerm]): Set[FOLTerm] = {
    val renaming: Map[Expr, Expr] =
      (constants.nonLogical(termset).toSeq ++ freeVariables(termset).toSeq).sortBy(_.toString).zipWithIndex.map { case (c, i) => c -> Const(s"f$i", c.ty) }.toMap
    termset.map(TermReplacement(_, renaming).asInstanceOf[FOLTerm])
  }

  def termToString(t: FOLTerm): String = t match {
    case FOLConst(f)          => s"$f"
    case FOLFunction(f, args) => s"$f(${args map termToString mkString ","})"
  }

  def writeTermset(outFile: Path, termset: Set[FOLTerm]) =
    write.over(outFile, termset.map(termToString).toSeq.sorted.map(_ + "\n").mkString)

  val expansionProof = loadExpansionProof(inputPath)
  val encoding = InstanceTermEncoding(expansionProof.shallow, Ti)
  val termSet = encoding.encode(expansionProof).map(_.asInstanceOf[FOLTerm])
  writeTermset(outputPath, simplifyNames(termSet))
}
