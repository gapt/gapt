package at.logic.gapt.formats.tptp

import at.logic.gapt.expr.{ Bottom, FOLFormula }
import at.logic.gapt.expr.hol.{ univclosure, CNFn, CNFp }
import at.logic.gapt.proofs.{ Sequent, FOLClause }
import at.logic.gapt.proofs.sketch.{ SketchAxiom, SketchInference, RefutationSketch }

import scala.collection.mutable

class TptpProofParser extends TPTPParser {
  type StepList = Seq[( String, ( String, String, FOLFormula, List[GeneralTerm] ) )]

  def comment: Parser[Unit] = """[#%](.*)(\n|\r\n)""".r ^^ { _ => () }

  def step: Parser[( String, ( String, String, FOLFormula, List[GeneralTerm] ) )] = ( "cnf" | "fof" ) ~ "(" ~ name ~ "," ~ name ~ "," ~ formula ~ ( "," ~> general_term ).* ~ ")." ^^ {
    case lang ~ _ ~ num ~ _ ~ name ~ _ ~ clause ~ just ~ _ =>
      num -> ( lang, name, clause, just )
  }

  sealed trait GeneralTerm
  case class GTList( elements: Seq[GeneralTerm] ) extends GeneralTerm
  case class GTFun( name: String, args: Seq[GeneralTerm] ) extends GeneralTerm
  case class GTInt( int: Int ) extends GeneralTerm

  def general_term: Parser[GeneralTerm] = "[" ~> repsep( general_term, "," ).^^ { GTList( _ ) } <~ "]" |
    ( name.^^ { GTFun( _, Seq() ) } <~ ":" <~ general_term ) | variable.^^ { v => GTFun( v.name, Seq() ) } |
    ( "$fot" ~ "(" ~ term ~ ")" ^^ { _ => GTFun( "$fot", Seq() ) } ) |
    ( "$cnf" ~ "(" ~ formula ~ ")" ^^ { _ => GTFun( "$fot", Seq() ) } ) |
    ( name ~ opt( "(" ~> repsep( general_term, "," ) <~ ")" ) ^^ { case ( f ~ a ) => GTFun( f, a.getOrElse( Nil ) ) } ) | integer.^^ { GTInt }

  def tptpProof: Parser[StepList] = ( comment ^^ { _ => Seq() } | step ^^ { Seq( _ ) } ).* ^^ { _.flatten }
}

object TptpProofParser extends TptpProofParser {
  def parse( out: String, labelledCNF: Map[String, Seq[FOLClause]] ): RefutationSketch =
    parseAll( tptpProof, out ) match {
      case Success( result, _ ) =>
        parseSteps( result, labelledCNF )
    }

  def parse( out: String ): ( Sequent[FOLFormula], RefutationSketch ) =
    parseAll( tptpProof, out ) match {
      case Success( stepList_, _ ) =>
        val stepList = inventSources( stepList_ )
        val ( endSequent, labelledCNF ) = extractEndSequentAndCNF( stepList )
        endSequent -> parseSteps( stepList, labelledCNF )
    }

  def inventSources( stepList: StepList ): StepList = stepList map {
    case ( label, ( lang, role @ ( "axiom" | "hypothesis" | "conjecture" | "negated_conjecture" ), formula, Seq() ) ) =>
      label -> ( lang, role, formula, List( GTFun( "file", List( GTFun( "", List() ), GTFun( s"source_$label", List() ) ) ) ) )
    case ( label, ( lang, role @ ( "axiom" | "hypothesis" | "conjecture" | "negated_conjecture" ), formula, GTFun( "file", List( _, GTFun( "unknown", _ ) ) ) +: _ ) ) =>
      label -> ( lang, role, formula, List( GTFun( "file", List( GTFun( "", List() ), GTFun( s"source_$label", List() ) ) ) ) )
    case other => other
  }

  def extractEndSequentAndCNF( stepList: StepList ): ( Sequent[FOLFormula], Map[String, Seq[FOLClause]] ) = {
    var endSequent = Sequent[FOLFormula]()
    var labelledCNF = Map[String, Seq[FOLClause]]()

    stepList.map( _._2 ) foreach {
      case ( "fof", "conjecture", formula, List( GTFun( "file", List( _, GTFun( label, List() ) ) ) ) ) =>
        endSequent :+= formula
        labelledCNF += label -> CNFn.toClauseList( formula )
      case ( lang, _, formula, List( GTFun( "file", List( _, GTFun( label, List() ) ) ) ) ) =>
        endSequent +:= ( if ( lang == "cnf" ) univclosure( formula ) else formula )
        labelledCNF += label -> CNFp.toClauseList( formula )
      case _ =>
    }

    endSequent -> labelledCNF
  }

  def parseSteps( stepList: StepList, labelledCNF: Map[String, Seq[FOLClause]] ): RefutationSketch = {
    val steps = stepList.toMap

    def getParents( justification: GeneralTerm ): Seq[String] = justification match {
      case GTFun( "inference", List( _, _, GTList( parents ) ) )     => parents flatMap getParents
      case GTFun( "introduced", List( GTFun( "tautology", _ ), _ ) ) => Seq()
      case GTFun( "theory", GTFun( "equality", _ ) +: _ )            => Seq()
      case GTFun( parent, List() )                                   => Seq( parent )
    }

    val memo = mutable.Map[String, Seq[RefutationSketch]]()
    def convert( stepName: String ): Seq[RefutationSketch] = memo.getOrElseUpdate( stepName, steps( stepName ) match {
      case ( "fof", "conjecture", _, GTFun( "file", List( _, GTFun( label, _ ) ) ) +: _ ) =>
        labelledCNF( label ) map SketchAxiom
      case ( _, _, axiom, GTFun( "file", List( _, GTFun( label, _ ) ) ) +: _ ) =>
        CNFp.toClauseList( axiom ) match {
          case Seq( axiomClause ) =>
            Seq( SketchInference(
              axiomClause,
              labelledCNF( label ) map SketchAxiom
            ) )
          case clauses => labelledCNF( label ) map SketchAxiom
        }
      case ( _, _, conclusion, justification +: _ ) =>
        CNFp.toClauseList( conclusion ) match {
          case Seq( conclusionClause ) =>
            val sketchParents = getParents( justification ) flatMap convert
            Seq( SketchInference( conclusionClause, sketchParents ) )
          case clauses => getParents( justification ) flatMap convert
        }
    } )

    convert( stepList.find( _._2._3 == Bottom() ).get._1 ).head

  }
}
