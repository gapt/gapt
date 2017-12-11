package at.logic.gapt.provers.prover9

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.conversion.IvyToResolution
import at.logic.gapt.formats.prover9.{ Prover9TermParser, Prover9TermParserLadrStyle }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, Maybe, runProcess }

import scala.collection.mutable.ArrayBuffer

object Prover9 extends Prover9( extraCommands = _ => Seq() )
class Prover9( val extraCommands: ( Map[Const, Const] => Seq[String] ) = _ => Seq() ) extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( cnf: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( cnf.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val p9Input = toP9Input( cnf, renaming )
        runProcess.withExitValue( Seq( "prover9" ), p9Input ) match {
          case ( 0, out ) => Some( parseProof( out ) )
          case ( 2, _ )   => None
        }
      } ) map {
        mapInputClauses( _ ) { clause =>
          cnf.view flatMap { ourClause =>
            syntacticMatching( ourClause.toDisjunction, clause.toDisjunction ) map { Subst( Input( ourClause ), _ ) }
          } head
        }
      }

  private[prover9] def parseProof( p9Output: String ) = {
    val ivy = runProcess( Seq( "prooftrans", "ivy" ), p9Output )

    val ivyProof = IvyParser( StringInputFile( ivy ) )

    IvyToResolution( ivyProof )
  }

  private def toP9Input( cnf: Traversable[HOLClause], renaming: Map[Const, Const] ): String = {
    val commands = ArrayBuffer[String]()

    commands += "set(quiet)" // suppresses noisy output on stderr
    commands += "clear(auto_denials)" // prevents prover9 from exiting with error code 2 even though a proof was found
    commands ++= extraCommands( renaming )

    commands += "formulas(sos)"
    commands ++= cnf map toP9Input
    commands += "end_of_list"

    commands.map( _ + "." + sys.props( "line.separator" ) ).mkString
  }

  private def renameVars( formula: Expr ): Expr =
    Substitution( freeVariables( formula ).
      toSeq.zipWithIndex.map {
        case ( v, i ) => v -> FOLVar( s"x$i" )
      } )( formula )
  private def toP9Input( clause: HOLClause ): String = toP9Input( renameVars( clause.toDisjunction ) )
  private def toP9Input( expr: Expr ): String = expr match {
    case Top()                => "$T"
    case Bottom()             => "$F"
    case Neg( a )             => s"-${toP9Input( a )}"
    case Or( a, b )           => s"${toP9Input( a )} | ${toP9Input( b )}"
    case FOLAtom( f, as )     => toP9Input( f, as )
    case FOLFunction( f, as ) => toP9Input( f, as )
    case FOLVar( v )          => v
  }
  private def toP9Input( function: String, args: Seq[Expr] ): String =
    if ( args.isEmpty ) function else s"$function(${args.map( toP9Input ).mkString( "," )})"

  override val isInstalled: Boolean =
    try {
      runProcess.withExitValue( Seq( "prover9", "--help" ), "", true )._1 == 1
    } catch { case _: IOException => false }
}

object Prover9Importer extends ExternalProgram {
  override val isInstalled: Boolean = Prover9 isInstalled

  def robinsonProof( p9Output: InputFile ): ResolutionProof = {
    // The TPTP prover9 output files can't be read by prooftrans ivy directly...
    val fixedP9Output = runProcess(
      Seq( "prooftrans" ),
      loadExpansionProof.extractFromTSTPCommentsIfNecessary( p9Output ).read )

    Prover9 parseProof fixedP9Output
  }

  private def reconstructEndSequent( p9Output: String ): HOLSequent = {
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

  def robinsonProofWithReconstructedEndSequent( p9Output: InputFile ): ( ResolutionProof, HOLSequent ) = {
    val p9Output_ = loadExpansionProof.extractFromTSTPCommentsIfNecessary( p9Output )

    val resProof = robinsonProof( p9Output_ )
    val endSequent = existentialClosure {
      val tptpEndSequent = reconstructEndSequent( p9Output_.read )
      if ( containsStrongQuantifier( tptpEndSequent ) ) {
        // in this case the prover9 proof contains skolem symbols which we do not try to match
        resProof.subProofs.collect { case Input( seq ) => seq.toDisjunction } ++: Sequent()
      } else {
        formulaToSequent.pos( tptpEndSequent.toDisjunction )
      }
    }

    val fixedResProof = fixDerivation( resProof, endSequent )

    ( fixedResProof, endSequent )
  }

  def lkProof( p9Output: InputFile ): LKProof =
    ResolutionToLKProof( robinsonProofWithReconstructedEndSequent( p9Output )._1 )

  def expansionProof( p9Output: InputFile ): ExpansionProof =
    ResolutionToExpansionProof( robinsonProofWithReconstructedEndSequent( p9Output )._1 )
}