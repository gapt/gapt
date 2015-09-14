package at.logic.gapt.provers.eprover

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.formats.tptp.TPTPParser
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.{ HOLClause, FOLClause }
import at.logic.gapt.proofs.sketch.{ SketchInference, SketchAxiom, RefutationSketchToRobinson, RefutationSketch }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.sys.process._
import scala.collection.mutable

class EProverProver extends ResolutionProver with ExternalProgram {
  val backgroundProver = new Prover9Prover

  override def getRobinsonProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    withRenamedConstants( seq ) {
      case ( renaming, cnf ) =>
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = toTPTP( labelledCNF )
        val output = withTempFile.fromString( tptpIn ) { tptpInFile =>
          Seq( "eproof", "--tptp3-format", tptpInFile ) !!
        }
        if ( output.split( "\n" ).contains( "# SZS status Unsatisfiable" ) )
          RefutationSketchToRobinson( EProverOutputParser.parse( output, labelledCNF ), backgroundProver )
        else None
    }

  private def toTPTP( formula: LambdaExpression ): String = formula match {
    case Bottom()                  => "$false"
    case Or( a, b )                => s"${toTPTP( a )} | ${toTPTP( b )}"
    case Eq( a, b )                => s"${toTPTP( a )}=${toTPTP( b )}"
    case Neg( Eq( a, b ) )         => s"${toTPTP( a )}!=${toTPTP( b )}"
    case Neg( atom )               => s"~${toTPTP( atom )}"
    case FOLAtom( name, Seq() )    => name
    case FOLAtom( name, args )     => s"$name(${args map toTPTP mkString ","})"
    case FOLVar( name )            => name
    case FOLConst( name )          => name
    case FOLFunction( name, args ) => s"$name(${args map toTPTP mkString ","})"
  }

  def renameVars( formula: LambdaExpression ): LambdaExpression =
    Substitution( freeVariables( formula ).
      toSeq.zipWithIndex.map {
        case ( v, i ) => v -> FOLVar( s"X$i" )
      } )( formula )
  private def toTPTP( clause: FOLClause ): String =
    toTPTP( renameVars( clause.toFormula ) )

  private def toTPTP( cnf: Map[String, FOLClause] ): String =
    cnf.map {
      case ( label, clause ) =>
        s"cnf($label, axiom, ${toTPTP( clause )})."
    }.mkString( sys.props( "line.separator" ) )

  override val isInstalled: Boolean = backgroundProver.isInstalled &&
    ( try {
      "eproof --version".!!
      true
    } catch {
      case ex: IOException => false
    } )
}

class EProverOutputParser extends TPTPParser {
  def comment: Parser[Unit] = """# (.*)\n""".r ^^ { _ => () }

  def step: Parser[( String, ( String, FOLClause, List[GeneralTerm] ) )] = "cnf(" ~ name ~ "," ~ name ~ "," ~ formula ~ ( "," ~> general_term ).* ~ ")." ^^ {
    case _ ~ num ~ _ ~ name ~ _ ~ clause ~ just ~ _ =>
      num -> ( name, CNFp.toClauseList( clause ).head, just )
  }

  sealed trait GeneralTerm
  case class GTList( elements: Seq[GeneralTerm] ) extends GeneralTerm
  case class GTFun( name: String, args: Seq[GeneralTerm] ) extends GeneralTerm
  case class GTInt( int: Int ) extends GeneralTerm

  def general_term: Parser[GeneralTerm] = "[" ~> repsep( general_term, "," ).^^ { GTList( _ ) } <~ "]" |
    ( name ~ opt( "(" ~> repsep( general_term, "," ) <~ ")" ) ^^ { case ( f ~ a ) => GTFun( f, a.getOrElse( Nil ) ) } ) | integer.^^ { GTInt }

  def eproverOutput: Parser[Seq[( String, ( String, FOLClause, List[GeneralTerm] ) )]] = ( comment ^^ { _ => Seq() } | step ^^ { Seq( _ ) } ).* ^^ { _.flatten }
}

object EProverOutputParser extends EProverOutputParser {
  def parse( out: String, labelledCNF: Map[String, FOLClause] ): RefutationSketch =
    parseAll( eproverOutput, out ) match {
      case Success( result, _ ) =>
        val steps = result.toMap

        val memo = mutable.Map[String, RefutationSketch]()
        def convert( stepName: String ): RefutationSketch = memo.getOrElseUpdate( stepName, steps( stepName ) match {
          case ( "axiom", axiom, List( GTFun( "file", List( _, GTFun( label, _ ) ) ) ) ) =>
            SketchInference( axiom, Seq( SketchAxiom( labelledCNF( label ) ) ) )
          case ( "plain", conclusion, List( GTFun( "inference", List( _, _, GTList( parents ) ) ) ) ) =>
            val sketchParents = parents map { case GTFun( parentName, List() ) => convert( parentName ) }
            SketchInference( conclusion, sketchParents )
          case ( "plain", _, List( GTFun( parent, _ ), GTList( List( GTFun( "proof", _ ) ) ) ) ) =>
            convert( parent )
        } )

        convert( result.last._1 )
    }
}
