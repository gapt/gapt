package at.logic.gapt.formats.llk

import at.logic.gapt.expr.{ LambdaExpression, HOLFormula }
import at.logic.gapt.formats.llkNew.LLKFormulaParser
import at.logic.gapt.proofs.lkOld.base.LKProof
import java.io.{ BufferedWriter => JBufferedWriter, FileWriter => JFileWriter }

/**
 * Top-level interface to LLK Parsing
 */

object loadLLK {
  def apply() =
    """loadLLK(path:String) : ExtendedProofDatabase.
      |
      |Load an LLK proof from path and return its proof database.
      |""".stripMargin
  def apply( filename: String ): ExtendedProofDatabase = {
    val tokens = HybridLatexParser.parseFile( filename )
    HybridLatexParser.createLKProof( tokens )
  }
}

object exportLLK {
  def apply() =
    """exportLLK(p:LKProof, path : String).
      |
      |Export an LLK proof p to the file at path.
      |
      |exportLLK(p:LKProof, enable_latex : Boolean = true) : String.
      |Return the LLK representation of p. Set enable_latex to false for better readability.
      | loadLLK recognizes both styles.
    """.stripMargin
  def apply( lkproof: LKProof, enable_latex: Boolean ) = HybridLatexExporter( lkproof, enable_latex )
  def apply( lkproof: LKProof ) = HybridLatexExporter( lkproof, true )
  def apply( lkproof: LKProof, filename: String ) = {
    val file = new JBufferedWriter( new JFileWriter( filename ) )
    file.write( HybridLatexExporter( lkproof, true ) )
    file.close
  }
}

object parseLLKExp {
  def apply() =
    """parseLLKExp(s:String) : LambdaExpression
    |
    |Parse a higher-order expression in the LLK format.
  """.stripMargin

  def apply( s: String ): LambdaExpression = { LLKFormulaParser.parse( s ) }
}

object parseLLKFormula {
  def apply() =
    """parseLLKExp(s:String) : HOLFormula
    |
    |Parse a higher-order formula in the LLK format.
  """.stripMargin

  def apply( s: String ) = {
    val exp = LLKFormulaParser.parse( s )
    require( exp.isInstanceOf[HOLFormula], "Expression is no HOL Formula!" )
    exp.asInstanceOf[HOLFormula]
  }
}
