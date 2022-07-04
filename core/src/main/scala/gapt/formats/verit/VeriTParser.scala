package gapt.formats.verit

import gapt.formats.InputFile
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.proofs.expansion._
import gapt.provers.verit.FormulaInstance
import gapt.provers.verit.aletheQfUf

import java.io.{ Reader, StringReader }
import scala.util.parsing.combinator._

class VeriTParserException( msg: String ) extends Exception( msg: String )
class VeriTUnfoldingTransitivityException( msg: String ) extends Exception( msg: String )

object VeriTParser extends RegexParsers with AletheParser {

  def getExpansionProof( file: InputFile ): Option[ExpansionSequent] = {
    getExpansionProof( new StringReader( file.read ) )
  }

  def getExpansionProof( in: Reader ): Option[ExpansionSequent] = {
    parseProof( in ) map { aletheProof =>
      val inputFormulas = aletheQfUf.collectUsedInputFormulas( aletheProof, Map() )
      val equalityInstances = aletheQfUf.collectEqualityInstances( aletheProof, Map() )
      val equalityExpansionTrees = equalityInstances
        .groupBy { case FormulaInstance( f, ts ) => ( f, ts.size ) }
        .map {
          case ( ( ax, vs ), instances ) =>
            ETWeakQuantifierBlock(
              ax,
              vs,
              instances.map { i => ( i.terms, formulaToExpansionTree( i.instance, Polarity.InAntecedent ) ) } )
        }

      inputFormulas.map { formulaToExpansionTree( _, Polarity.InAntecedent ) } ++: equalityExpansionTrees ++: Sequent()
    }
  }

  def getExpansionProofWithSymmetry( file: InputFile ): Option[ExpansionSequent] =
    getExpansionProof( file ) map { addSymmetry( _ ) }

  def isUnsat( file: InputFile ): Boolean =
    isUnsat( new StringReader( file.read ) )

  def isUnsat( reader: Reader ): Boolean = {
    parseAll( parseUnsat, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new VeriTParserException(
          s"VeriT parsing: syntax failure $msg\nat line ${next.pos.line} and column ${next.pos.column}" )
      case Error( msg, next ) =>
        throw new VeriTParserException(
          s"VeriT parsing: syntax error $msg\nat line ${next.pos.line} and column ${next.pos.column}" )
    }
  }

  def parseProof( input: String ): Option[AletheProof] =
    parseProof( new StringReader( input ) )

  def parseProof( input: Reader ): Option[AletheProof] =
    parseAll( proof, input ) match {
      case Success( p, _ ) => p
      case e: NoSuccess =>
        throw new VeriTParserException( s"VeriT parser error: syntax error '${e.msg}' at ${e.next.pos}\n${e}" )
    }

  def proof: Parser[Option[AletheProof]] = {
    ( unsat ~> aletheProof ^^ { p => Some( p ) } ) | sat ~ sat_message ^^ { _ => None }
  }

  def unsat: Parser[String] = "unsat"

  def parseUnsat: Parser[Boolean] =
    ( unsat ^^ ( _ => true ) | sat ^^ ( _ => false ) )

  def sat: Parser[String] = "sat"

  def sat_message: Parser[String] = "Formula is Satisfiable"
}
