package at.logic.gapt.formats.tip

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.hol.isPrenex
import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParser
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.utils.withTempFile
import scala.collection.mutable
import scala.sys.process._

object TipParser {
  private def parseLADR( contents: String ): HOLSequent = {
    val antecedent = mutable.Buffer[HOLFormula]()
    val succedent = mutable.Buffer[HOLFormula]()

    var currentBuffer = antecedent

    val formulaParser = Prover9TermParser
    val formulaLine = """([^#.]+)#.*""".r

    contents.split( sys.props( "line.separator" ) ) foreach {
      case "formulas(assumptions)." => currentBuffer = antecedent
      case "formulas(goals)."       => currentBuffer = succedent
      case formulaLine( formula )   => currentBuffer += formulaParser.parseFormula( formula )
      case x                        => ()
    }

    HOLSequent( antecedent, succedent )
  }

  private def fixupConstants( seq: HOLSequent ): HOLSequent =
    seq map { TermReplacement( _, Map( FOLConst( "z" ) -> FOLConst( "0" ) ).toMap[LambdaExpression, LambdaExpression] ) }

  private def fixupNonPrenex( f: HOLFormula ): Seq[HOLFormula] = f match {
    case _ if isPrenex( f ) => Seq( f )
    case And( x, y )        => fixupNonPrenex( x ) ++ fixupNonPrenex( y )
    case All( v, g )        => fixupNonPrenex( g ).map( All( v, _ ) )
  }

  private def fixupNonPrenex( seq: HOLSequent ): HOLSequent =
    HOLSequent( seq.antecedent.flatMap( fixupNonPrenex ), seq.succedent )

  def parse( contents: String ): HOLSequent = {
    val ladr = withTempFile.fromString( contents ) { tipFile =>
      Seq( "tip", "--why", tipFile ) #|
        Seq( "why3", "prove", "-D", "eprover", "-F", "whyml", "-" ) #|
        Seq( "tptp_to_ladr" ) !!
    }

    fixupNonPrenex( fixupConstants( parseLADR( ladr ) ) )
  }
}