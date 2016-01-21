package at.logic.gapt.formats.latex

/**
 * Created with IntelliJ IDEA.
 * User: mishiko
 * Date: 9/6/12
 * Time: 21:49
 */

import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.base.{ BinaryLKProof, LKProof, NullaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.proofs.RuleTypeA
import at.logic.gapt.proofs.shlk.SchemaProofLinkRule
import at.logic.gapt.prooftool.DrawSequent
//import at.logic.calculi.lk.quantificationRules.{ForallRightRuleType, ForallLeftRuleType, ExistsRightRuleType, ExistsLeftRuleType}
//import at.logic.calculi.lk.definitionRules.{DefinitionRightRuleType, DefinitionLeftRuleType}
//import at.logic.calculi.lk.equationalRules.{EquationRight2RuleType, EquationRight1RuleType, EquationLeft2RuleType, EquationLeft1RuleType}

object ProofToLatexExporter {

  val nLine = sys.props( "line.separator" )

  def apply( proof: LKProof ) = document( proofToLatex( proof ) )

  def apply( list: List[( String, LKProof )] ) =
    document( list.foldLeft( "" )( ( s, pair ) => s + nLine + " The proof $" + pair._1 + "$ is:" + nLine + nLine + proofToLatex( pair._2 ) ) )

  def document( body: String ) =
    "\\documentclass{memoir} " + nLine + " " + nLine +
      "% Change the values to fit the proof in one 'page'. " + nLine +
      "% Default size is A4 paper. " + nLine +
      "\\setstocksize{297mm}{210mm} " + nLine +
      "\\settrimmedsize{\\stockheight}{\\stockwidth}{*} " + nLine + " " + nLine +
      "\\usepackage{fullpage} " + nLine +
      "\\usepackage{amssymb} " + nLine +
      "\\usepackage{bussproofs} " + nLine +
      "\\pagestyle{empty} " + nLine +
      "\\begin{document} " + nLine +
      body +
      "\\end{document}"

  def proofToLatex( proof: LKProof ) =
    "\\begin{prooftree} " + nLine +
      rulesToLatex( proof ) +
      "\\end{prooftree} " + nLine

  def rulesToLatex( proof: LKProof ): String = proof match {
    case p: NullaryLKProof => p match {
      case SchemaProofLinkRule( root, link, indices ) =>
        "\\AxiomC{$(" + link + "(" + DrawSequent.formulaToLatexString( indices.head ) + "))$} " + nLine +
          "\\dashedLine " + nLine +
          "\\UnaryInfC{$" + DrawSequent.sequentToLatexString( root ) + "$} " + nLine
      case _ =>
        "\\AxiomC{$" + DrawSequent.sequentToLatexString( p.root ) + "$} " + nLine
    }
    case p: UnaryLKProof =>
      rulesToLatex( p.uProof ) +
        "\\RightLabel{$" + ruleNameToLatex( p.rule ) + "$} " + nLine +
        "\\UnaryInfC{$" + DrawSequent.sequentToLatexString( p.root ) + "$} " + nLine
    case p: BinaryLKProof =>
      rulesToLatex( p.uProof1 ) + nLine +
        rulesToLatex( p.uProof2 ) + nLine +
        "\\RightLabel{$" + ruleNameToLatex( p.rule ) + "$} " + nLine +
        "\\BinaryInfC{$" + DrawSequent.sequentToLatexString( p.root ) + "$} " + nLine
  }

  def ruleNameToLatex( name: RuleTypeA ) = name match {
    case NegLeftRuleType          => "\\neg \\colon l"
    case NegRightRuleType         => "\\neg \\colon r"
    case AndLeft1RuleType         => "\\land \\colon l1"
    case AndLeft2RuleType         => "\\land \\colon l2"
    case AndRightRuleType         => "\\land \\colon r"
    case OrLeftRuleType           => "\\lor \\colon l"
    case OrRight1RuleType         => "\\lor \\colon r1"
    case OrRight2RuleType         => "\\lor \\colon r2"
    case ImpLeftRuleType          => "\\supset \\colon l"
    case ImpRightRuleType         => "\\supset \\colon r"
    case ExistsLeftRuleType       => "\\exists \\colon l"
    case ExistsRightRuleType      => "\\exists \\colon r"
    case ForallLeftRuleType       => "\\forall \\colon l"
    case ForallRightRuleType      => "\\forall \\colon r"
    case WeakeningLeftRuleType    => "w \\colon l"
    case WeakeningRightRuleType   => "w \\colon r"
    case ContractionLeftRuleType  => "c \\colon l"
    case ContractionRightRuleType => "c \\colon r"
    case CutRuleType              => "cut"
    case DefinitionLeftRuleType   => "d \\colon l"
    case DefinitionRightRuleType  => "d \\colon r"
    case EquationLeft1RuleType    => "e \\colon l1"
    case EquationLeft2RuleType    => "e \\colon l2"
    case EquationRight1RuleType   => "e \\colon r1"
    case EquationRight2RuleType   => "e \\colon r2"
    case _                        => "\\twoheadrightarrow"
  }
}
