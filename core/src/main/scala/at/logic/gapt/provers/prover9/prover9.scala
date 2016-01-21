package at.logic.gapt.provers.prover9

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.formats.prover9.{ Prover9TermParserLadrStyle, Prover9TermParser }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.ExpansionSequent
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.runProcess

import scala.collection.mutable.ArrayBuffer
import scala.io.Source

object Prover9 extends Prover9( extraCommands = _ => Seq() )
class Prover9( val extraCommands: ( Map[Const, Const] => Seq[String] ) = _ => Seq() ) extends ResolutionProver with ExternalProgram {
  def getRobinsonProof( cnf: Traversable[HOLClause] ): Option[ResolutionProof] =
    withRenamedConstants( cnf ) {
      case ( renaming, cnf ) =>
        val p9Input = toP9Input( cnf, renaming )
        runProcess.withExitValue( Seq( "prover9" ), p9Input ) match {
          case ( 0, out ) => Some( parseProof( out ) )
          case ( 2, _ )   => None
        }
    } map {
      mapInputClauses( _ ) { clause =>
        cnf.view flatMap { ourClause =>
          syntacticMatching( ourClause.toFormula.asInstanceOf[FOLFormula], clause.toFormula.asInstanceOf[FOLFormula] ) map { matching =>
            Instance( InputClause( ourClause.map { _.asInstanceOf[FOLAtom] } ), matching )
          }
        } head
      }
    }

  private[prover9] def parseProof( p9Output: String ) = {
    val ivy = runProcess( Seq( "prooftrans", "ivy" ), p9Output )

    val ivyProof = IvyParser.parseString( ivy )

    IvyToRobinson( ivyProof )
  }

  private def toP9Input( cnf: List[HOLClause], renaming: Map[Const, Const] ): String = {
    val commands = ArrayBuffer[String]()

    commands += "set(quiet)" // suppresses noisy output on stderr
    commands += "clear(auto_denials)" // prevents prover9 from exiting with error code 2 even though a proof was found
    commands ++= extraCommands( renaming )

    commands += "formulas(sos)"
    commands ++= cnf map toP9Input
    commands += "end_of_list"

    commands.map( _ + "." + sys.props( "line.separator" ) ).mkString
  }

  private def renameVars( formula: LambdaExpression ): LambdaExpression =
    Substitution( freeVariables( formula ).
      toSeq.zipWithIndex.map {
        case ( v, i ) => v -> FOLVar( s"x$i" )
      } )( formula )
  private def toP9Input( clause: HOLClause ): String = toP9Input( renameVars( clause.toFormula ) )
  private def toP9Input( expr: LambdaExpression ): String = expr match {
    case Top()                => "$T"
    case Bottom()             => "$F"
    case Neg( a )             => s"-${toP9Input( a )}"
    case Or( a, b )           => s"${toP9Input( a )} | ${toP9Input( b )}"
    case FOLAtom( f, as )     => toP9Input( f, as )
    case FOLFunction( f, as ) => toP9Input( f, as )
    case FOLVar( v )          => v
  }
  private def toP9Input( function: String, args: Seq[LambdaExpression] ): String =
    if ( args.isEmpty ) function else s"$function(${args.map( toP9Input ).mkString( "," )})"

  override val isInstalled: Boolean =
    try {
      runProcess.withExitValue( Seq( "prover9", "--help" ), "", true )._1 == 1
    } catch { case _: IOException => false }
}

object Prover9Importer extends ExternalProgram {
  override val isInstalled: Boolean = Prover9 isInstalled

  def robinsonProofFromFile( p9File: String ): ResolutionProof =
    robinsonProof( Source fromFile p9File mkString )

  def robinsonProof( p9Output: String ): ResolutionProof = {
    // The TPTP prover9 output files can't be read by prooftrans ivy directly...
    val fixedP9Output = runProcess( Seq( "prooftrans" ), p9Output )

    Prover9 parseProof fixedP9Output
  }

  def robinsonProofWithReconstructedEndSequentFromFile( p9File: String ): ( ResolutionProof, HOLSequent ) =
    robinsonProofWithReconstructedEndSequent( Source fromFile p9File mkString )

  def reconstructEndSequent( p9Output: String ): HOLSequent = {
    val lines = p9Output split "\n" toSeq

    val parser = if ( lines contains "set(prolog_style_variables)." )
      Prover9TermParser
    else
      Prover9TermParserLadrStyle

    val proof_start = """=+ (PROOF) =+""".r
    val proof_end = """=+ (end) of proof =+""".r
    val linesInProof = lines dropWhile {
      case proof_start( _ ) => false
      case _                => true
    } drop 1 takeWhile {
      case proof_end( _ ) => false
      case _              => true
    }
    val assumption = """(\d+) ([^#.]+).*\[assumption\]\.""".r
    val assumptions = linesInProof collect {
      case assumption( id, formula ) => parser parseFormula formula
    }
    val goal = """(\d+) ([^#.]+).*\[goal\]\.""".r
    val goals = linesInProof collect {
      case goal( id, formula ) => parser parseFormula formula
    }

    assumptions ++: Sequent() :++ goals distinct
  }

  def robinsonProofWithReconstructedEndSequent( p9Output: String ): ( ResolutionProof, HOLSequent ) = {
    val resProof = robinsonProof( p9Output )
    val endSequent = existsclosure {
      val tptpEndSequent = reconstructEndSequent( p9Output )
      if ( containsStrongQuantifier( tptpEndSequent ) ) {
        // in this case the prover9 proof contains skolem symbols which we do not try to match
        inputClauses( resProof ).map( _.toFormula ) ++: Sequent()
      } else {
        prenexify.pos( tptpEndSequent.toFormula )
      }
    }

    val fixedResProof = fixDerivation( resProof, endSequent )

    ( fixedResProof, endSequent )
  }

  def lkProofFromFile( p9File: String ): LKProof =
    lkProof( Source fromFile p9File mkString )

  def lkProof( p9Output: String ): LKProof = {
    val ( fixedResProof, endSequent ) = robinsonProofWithReconstructedEndSequent( p9Output )
    RobinsonToLK( fixedResProof, endSequent )
  }

  def expansionProofFromFile( p9File: String ): ExpansionSequent =
    expansionProof( Source.fromFile( p9File ).mkString )

  def expansionProof( p9Output: String ): ExpansionSequent = {
    val ( fixedResProof, endSequent ) = robinsonProofWithReconstructedEndSequent( p9Output )
    RobinsonToExpansionProof( fixedResProof, endSequent ).expansionSequent
  }
}