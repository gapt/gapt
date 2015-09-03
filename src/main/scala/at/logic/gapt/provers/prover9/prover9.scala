package at.logic.gapt.provers.prover9

import java.io.{ IOException, ByteArrayInputStream, ByteArrayOutputStream }

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ containsStrongQuantifier, existsclosure, univclosure, CNFn }
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.IvyParser.IvyStyleVariables
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.proofs.expansionTrees.ExpansionSequent
import at.logic.gapt.proofs.lk.applyReplacement
import at.logic.gapt.proofs.lk.base.{ LKProof, HOLSequent }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.robinson.RobinsonResolutionProof
import at.logic.gapt.provers.prover9.commands.InferenceExtractor
import at.logic.gapt.provers.{ ResolutionProver, groundFreeVariables, renameConstantsToFi, Prover }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.sys.process._

class Prover9Prover( val extraCommands: ( Map[Const, String] => Seq[String] ) = ( _ => Seq() ) ) extends ResolutionProver with ExternalProgram {
  def getRobinsonProof( cnf: Traversable[HOLClause] ): Option[RobinsonResolutionProof] =
    withRenamedConstants( cnf ) {
      case ( renaming, cnf ) =>
        val p9Input = toP9Input( cnf, renaming )
        withTempFile.fromString( p9Input ) { p9InputFile =>
          val out = new ByteArrayOutputStream
          Seq( "prover9", "-f", p9InputFile ) #> out ! match {
            case 0 => Some( out toString )
            case 2 => None
          }
        } map parseProof
    }

  def parseProof( p9Output: String ) = {
    val ivy = withTempFile.fromString( p9Output ) { p9OutputFile =>
      Seq( "prooftrans", "ivy", "-f", p9OutputFile ) !!
    }

    val ivyProof = withTempFile.fromString( ivy ) { ivyFile => IvyParser( ivyFile, IvyStyleVariables ) }

    IvyToRobinson( ivyProof )
  }

  @deprecated( "Use Prover9Importer.robinsonProof instead" )
  def reconstructRobinsonProofFromFile( p9File: String ): RobinsonResolutionProof =
    Prover9Importer robinsonProofFromFile p9File

  @deprecated( "Use Prover9Importer.robinsonProof instead" )
  def reconstructRobinsonProofFromOutput( p9Output: String ): RobinsonResolutionProof =
    Prover9Importer robinsonProof p9Output

  @deprecated( "Use Prover9Importer.lkProof instead" )
  def reconstructLKProofFromFile( p9File: String ): LKProof =
    Prover9Importer lkProofFromFile p9File

  @deprecated( "Use Prover9Importer.lkProof instead" )
  def reconstructLKProofFromOutput( p9Output: String ): LKProof =
    Prover9Importer lkProof p9Output

  def toP9Input( cnf: List[HOLClause], renaming: Map[Const, String] ): String = {
    val commands = ArrayBuffer[String]()

    commands += "set(quiet)" // suppresses noisy output on stderr
    commands += "clear(auto_denials)" // prevents prover9 from exiting with error code 2 even though a proof was found
    commands ++= extraCommands( renaming )

    commands += "formulas(sos)"
    commands ++= cnf map toP9Input
    commands += "end_of_list"

    commands.map( _ + "." + sys.props( "line.separator" ) ).mkString
  }

  def renameVars( formula: LambdaExpression ): LambdaExpression =
    Substitution( freeVariables( formula ).
      toSeq.zipWithIndex.map {
        case ( v, i ) => v -> FOLVar( s"x$i" )
      } )( formula )
  def toP9Input( clause: HOLClause ): String = toP9Input( renameVars( clause.toFormula ) )
  def toP9Input( expr: LambdaExpression ): String = expr match {
    case Neg( a )             => s"-${toP9Input( a )}"
    case Or( a, b )           => s"${toP9Input( a )} | ${toP9Input( b )}"
    case Bottom()             => "$F"
    case FOLAtom( f, as )     => toP9Input( f, as )
    case FOLFunction( f, as ) => toP9Input( f, as )
    case FOLVar( v )          => v
  }
  def toP9Input( function: String, args: Seq[LambdaExpression] ): String =
    if ( args.isEmpty ) function else s"$function(${args.map( toP9Input ).mkString( "," )})"

  override val isInstalled: Boolean =
    try {
      ( "prover9 --help" ! ProcessLogger( _ => () ) ) == 1
    } catch { case _: IOException => false }
}

object Prover9Importer extends ExternalProgram {
  private val p9 = new Prover9Prover
  override val isInstalled: Boolean = p9.isInstalled

  def robinsonProofFromFile( p9File: String ): RobinsonResolutionProof =
    robinsonProof( Source fromFile p9File mkString )

  def robinsonProof( p9Output: String ): RobinsonResolutionProof = {
    // The TPTP prover9 output files can't be read by prooftrans ivy directly...
    val fixedP9Output = withTempFile.fromString( p9Output ) { p9OutputFile =>
      Seq( "prooftrans", "-f", p9OutputFile ) !!
    }

    p9 parseProof fixedP9Output
  }

  def robinsonProofWithReconstructedEndSequentFromFile( p9File: String ): ( RobinsonResolutionProof, HOLSequent ) =
    robinsonProofWithReconstructedEndSequent( Source fromFile p9File mkString )

  def robinsonProofWithReconstructedEndSequent( p9Output: String ): ( RobinsonResolutionProof, HOLSequent ) = {
    val resProof = robinsonProof( p9Output )
    val endSequent = existsclosure( withTempFile.fromString( p9Output ) { p9File =>
      val tptpEndSequent = InferenceExtractor.viaLADR( p9File )
      if ( containsStrongQuantifier( tptpEndSequent ) ) {
        // in this case the prover9 proof contains skolem symbols which we do not try to match
        InferenceExtractor.clausesViaLADR( p9File )
      } else {
        tptpEndSequent
      }
    } )

    val ourCNF = CNFn.toFClauseList( endSequent.toFormula )

    val fixedResProof = fixDerivation( resProof, ourCNF )

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
    RobinsonToExpansionProof( fixedResProof, endSequent )
  }
}