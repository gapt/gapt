package gapt.formats.llk

import gapt.expr.{ Expr }
import gapt.proofs.lk.LKProof
import os._
import gapt.expr.formula.Formula
import gapt.formats.InputFile

/**
 * Top-level interface to LLK Parsing
 */

object loadLLK {
  def apply() =
    """loadLLK(path:String) : ExtendedProofDatabase.
      |
      |Load an LLK proof from path and return its proof database.
      |""".stripMargin
  def apply( filename: InputFile ): ExtendedProofDatabase = LLKProofParser( filename )
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
  def apply( lkproof: LKProof, enable_latex: Boolean ) = LLKExporter( lkproof, enable_latex )
  def apply( lkproof: LKProof ) = LLKExporter( lkproof, true )
  def apply( lkproof: LKProof, filename: String ) = write( Path( filename, pwd ), LLKExporter( lkproof, true ) )
}

object parseLLKExp {
  def apply() =
    """parseLLKExp(s:String) : Expr
    |
    |Parse a higher-order expression in the LLK format.
  """.stripMargin

  def apply( s: String ): Expr = { LLKFormulaParser.parse( s ) }
}

object parseLLKFormula {
  def apply() =
    """parseLLKExp(s:String) : Formula
    |
    |Parse a higher-order formula in the LLK format.
  """.stripMargin

  def apply( s: String ) = {
    val exp = LLKFormulaParser.parse( s )
    require( exp.isInstanceOf[Formula], "Expression is no HOL Formula!" )
    exp.asInstanceOf[Formula]
  }
}

/**
 * A package with shortcuts for parsing higher-order functions. They are separate because the short names might
 * pollute the namespace.
 */
package short {
  import gapt.formats.llk.LLKTypes.LLKSignature

  object sig { def apply( s: String ): LLKSignature = DeclarationParser.parseDeclaration( s ) }

  object hot {
    def apply( s: String )( implicit signature: LLKSignature ) = {
      DeclarationParser.parseAll( DeclarationParser.formula, s ) match {
        case DeclarationParser.Success( result, _ ) => LLKFormulaParser.ASTtoHOL( signature.apply, result )
        case failure: DeclarationParser.NoSuccess =>
          throw new Exception( "Error parsing HOL formula '" +
            s + "' at position " + failure.next.pos + ". Error message: " + failure.msg )
      }
    }
  }

  object hof {
    def apply( s: String )( implicit signature: LLKSignature ) = hot( s )( signature ) match {
      case f: Formula => f
      case e: Expr    => throw new Exception( s"ef is an expression of type ${e.ty} but not a formula!" )
    }
  }

}
