package at.logic.gui.prooftool.parser

/**
 * Created with IntelliJ IDEA.
 * User: mishiko
 * Date: 9/6/12
 * Time: 21:49
 */

import at.logic.calculi.lk.base.{NullaryLKProof, BinaryLKProof, UnaryLKProof, LKProof}
import at.logic.calculi.proofs.RuleTypeA
import at.logic.gui.prooftool.gui.DrawSequent
import at.logic.calculi.lk._
import at.logic.calculi.slk.SchemaProofLinkRule
//import at.logic.calculi.lk.quantificationRules.{ForallRightRuleType, ForallLeftRuleType, ExistsRightRuleType, ExistsLeftRuleType}
//import at.logic.calculi.lk.definitionRules.{DefinitionRightRuleType, DefinitionLeftRuleType}
//import at.logic.calculi.lk.equationalRules.{EquationRight2RuleType, EquationRight1RuleType, EquationLeft2RuleType, EquationLeft1RuleType}


object ProofToLatexExporter {

  def apply(proof: LKProof) = document(proofToLatex(proof))

  def apply(list: List[(String,LKProof)]) =
    document(list.foldLeft("")((s, pair) => s + "\n The proof $" + pair._1 + "$ is:\n\n" + proofToLatex(pair._2)))

  def document(body: String) =
    "\\documentclass{memoir} \n \n" +
    "% Change the values to fit the proof in one 'page'. \n" +
    "% Default size is A4 paper. \n" +
    "\\setstocksize{297mm}{210mm} \n" +
    "\\settrimmedsize{\\stockheight}{\\stockwidth}{*} \n \n" +
    "\\usepackage{fullpage} \n" +
    "\\usepackage{amssymb} \n" +
    "\\usepackage{bussproofs} \n" +
    "\\pagestyle{empty} \n" +
    "\\begin{document} \n" +
    body +
    "\\end{document}"

  def proofToLatex(proof: LKProof) =
    "\\begin{prooftree} \n" +
    rulesToLatex(proof) +
    "\\end{prooftree} \n"

  def rulesToLatex(proof: LKProof): String = proof match {
    case p: NullaryLKProof => p match {
      case SchemaProofLinkRule(root, link, indices) =>
        "\\AxiomC{$(" + link + "(" + DrawSequent.formulaToLatexString(indices.head) + "))$} \n" +
        "\\dashedLine \n" +
        "\\UnaryInfC{$" + DrawSequent.sequentToLatexString(root) + "$} \n"
      case _ =>
        "\\AxiomC{$" + DrawSequent.sequentToLatexString(p.root) + "$} \n"
    }
    case p: UnaryLKProof =>
      rulesToLatex(p.uProof) +
      "\\RightLabel{$" + ruleNameToLatex(p.rule) + "$} \n" +
      "\\UnaryInfC{$" + DrawSequent.sequentToLatexString(p.root) + "$} \n"
    case p: BinaryLKProof =>
      rulesToLatex(p.uProof1) + "\n" +
      rulesToLatex(p.uProof2) + "\n" +
      "\\RightLabel{$" + ruleNameToLatex(p.rule) + "$} \n" +
      "\\BinaryInfC{$" + DrawSequent.sequentToLatexString(p.root) + "$} \n"
  }

  def ruleNameToLatex(name: RuleTypeA) = name match {
    case NegLeftRuleType => "\\neg \\colon l"
    case NegRightRuleType => "\\neg \\colon r"
    case AndLeft1RuleType => "\\land \\colon l1"
    case AndLeft2RuleType => "\\land \\colon l2"
    case AndRightRuleType => "\\land \\colon r"
    case OrLeftRuleType => "\\lor \\colon l"
    case OrRight1RuleType => "\\lor \\colon r1"
    case OrRight2RuleType => "\\lor \\colon r2"
    case ImpLeftRuleType => "\\supset \\colon l"
    case ImpRightRuleType => "\\supset \\colon r"
    case ExistsLeftRuleType => "\\exists \\colon l"
    case ExistsRightRuleType => "\\exists \\colon r"
    case ForallLeftRuleType => "\\forall \\colon l"
    case ForallRightRuleType => "\\forall \\colon r"
    case WeakeningLeftRuleType => "w \\colon l"
    case WeakeningRightRuleType => "w \\colon r"
    case ContractionLeftRuleType => "c \\colon l"
    case ContractionRightRuleType => "c \\colon r"
    case CutRuleType => "cut"
    case DefinitionLeftRuleType => "d \\colon l"
    case DefinitionRightRuleType => "d \\colon r"
    case EquationLeft1RuleType => "e \\colon l1"
    case EquationLeft2RuleType => "e \\colon l2"
    case EquationRight1RuleType => "e \\colon r1"
    case EquationRight2RuleType => "e \\colon r2"
    case _ => "\\twoheadrightarrow"
  }
}
