package at.logic.gapt.provers.eprover

import java.io.IOException

import at.logic.gapt.expr.{ FOLAtom, HOLAtom, Bottom, FOLFormula }
import at.logic.gapt.expr.hol.{ CNFp, dualize, CNFn }
import at.logic.gapt.formats.leanCoP.LeanCoPParserException
import at.logic.gapt.formats.tptp.{ TPTPParser, TPTPFOLExporter }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.{ HOLClause, FOLClause }
import at.logic.gapt.proofs.sketch.{ RefutationSketchToRobinson, RefutationSketch }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.sys.process._
import scala.util.parsing.combinator._

class EProverProver extends ResolutionProver with ExternalProgram {
  override def getRobinsonProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    withRenamedConstants( seq ) {
      case ( renaming, cnf ) =>
        val tptpIn = toTPTP( cnf.map( _.map( _.asInstanceOf[FOLAtom] ) ) )
        val output = withTempFile.fromString( tptpIn ) { tptpInFile =>
          Seq( "eproof-tptp", tptpInFile ) !!
        }
        RefutationSketchToRobinson( EProverOutputParser.parse( output ) )
    }

  private def toTPTP( cnf: List[FOLClause] ): String =
    cnf.zipWithIndex.map {
      case ( clause, index ) =>
        s"cnf(formula$index, axiom, ${TPTPFOLExporter.exportFormula( clause.toFormula.asInstanceOf[FOLFormula] )})."
    }.mkString( sys.props( "line.separator" ) )

  override val isInstalled: Boolean =
    try {
      "eprover --version".!!
      true
    } catch {
      case ex: IOException => false
    }
}

class EProverOutputParser extends TPTPParser {
  def comment: Parser[Unit] = """# (.*)\n""".r ^^ { _ => () }

  def step: Parser[( String, FOLClause )] = "cnf(" ~ integer ~ "," ~ name ~ "," ~ formula ~ ( "," ~> general_term ).* ~ ")." ^^ {
    case _ ~ num ~ _ ~ name ~ _ ~ clause ~ just ~ _ =>
      name -> CNFp.toClauseList( clause ).head
  }

  def general_term: Parser[Any] = "[" ~> repsep( general_term, "," ) <~ "]" |
    name ~ opt( "(" ~> repsep( general_term, "," ) <~ ")" ) | integer

  def eproverOutput: Parser[Seq[( String, FOLClause )]] = ( comment ^^ { _ => Seq() } | step ^^ { Seq( _ ) } ).* ^^ { _.flatten }
}

object EProverOutputParser extends EProverOutputParser {
  def parse( out: String ): RefutationSketch =
    parseAll( eproverOutput, out ) match {
      case Success( result, _ ) =>
        val axioms = result.collect { case ( "axiom", c ) => c }
        val steps = result.collect { case ( "plain", c ) => c }
        RefutationSketch( axioms.map( RefutationSketch.Step( _, RefutationSketch.Axiom ) ) ++
          steps.map( RefutationSketch.Step( _, RefutationSketch.ArbitraryInference ) ) )
    }
}
