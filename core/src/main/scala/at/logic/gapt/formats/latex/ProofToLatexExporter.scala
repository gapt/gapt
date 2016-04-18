package at.logic.gapt.formats.latex

import at.logic.gapt.formats.latex.LatexUIRenderer.{ formulaToLatexString, sequentToLatexString }
import at.logic.gapt.proofs.lk._

object ProofToLatexExporter {

  private val nLine = sys.props( "line.separator" )

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

  def rulesToLatex( p: LKProof ): String = p.immediateSubProofs.size match {
    case 0 =>
      "\\AxiomC{$" + sequentToLatexString( p.conclusion ) + "$} " + nLine
    case 1 =>
      rulesToLatex( p.immediateSubProofs( 0 ) ) +
        "\\RightLabel{$" + ruleNameToLatex( p ) + "$} " + nLine +
        "\\UnaryInfC{$" + sequentToLatexString( p.conclusion ) + "$} " + nLine
    case 2 =>
      rulesToLatex( p.immediateSubProofs( 0 ) ) + nLine +
        rulesToLatex( p.immediateSubProofs( 1 ) ) + nLine +
        "\\RightLabel{$" + ruleNameToLatex( p ) + "$} " + nLine +
        "\\BinaryInfC{$" + sequentToLatexString( p.conclusion ) + "$} " + nLine
  }

  def ruleNameToLatex( name: LKProof ) = name.name
}
