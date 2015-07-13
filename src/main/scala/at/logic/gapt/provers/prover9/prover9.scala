package at.logic.gapt.provers.prover9

import java.io.{ IOException, ByteArrayInputStream, ByteArrayOutputStream }

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ containsStrongQuantifier, existsclosure, univclosure, CNFn }
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.IvyParser.IvyStyleVariables
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.proofs.lk.applyReplacement
import at.logic.gapt.proofs.lk.base.{ LKProof, HOLSequent }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.robinson.RobinsonResolutionProof
import at.logic.gapt.provers.prover9.commands.InferenceExtractor
import at.logic.gapt.provers.{ groundFreeVariables, renameConstantsToFi, Prover }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.sys.process._

class Prover9Prover( val extraCommands: ( Map[Const, String] => Seq[String] ) = ( _ => Seq() ) ) extends Prover with ExternalProgram {
  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    withGroundVariables( seq ) { seq =>
      getRobinsonProof( seq ) map { robinsonProof =>
        RobinsonToLK( robinsonProof, seq )
      }
    }

  override def isValid( seq: HOLSequent ): Boolean =
    getRobinsonProof( groundFreeVariables( seq )._1 ).isDefined

  def getRobinsonProof( seq: HOLSequent ): Option[RobinsonResolutionProof] =
    getRobinsonProof( CNFn.toFClauseList( seq.toFormula ) )

  def getRobinsonProof( cnf: List[HOLClause] ): Option[RobinsonResolutionProof] =
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

  def reconstructRobinsonProofFromFile( p9File: String ): RobinsonResolutionProof =
    reconstructRobinsonProofFromOutput( Source.fromFile( p9File ).mkString )

  def reconstructRobinsonProofFromOutput( p9Output: String ): RobinsonResolutionProof = {
    // The TPTP prover9 output files can't be read by prooftrans ivy directly...
    val fixedP9Output = withTempFile.fromString( p9Output ) { p9OutputFile =>
      Seq( "prooftrans", "-f", p9OutputFile ) !!
    }

    parseProof( fixedP9Output )
  }

  def reconstructLKProofFromFile( p9File: String ): LKProof =
    reconstructLKProofFromOutput( Source.fromFile( p9File ).mkString )

  def reconstructLKProofFromOutput( p9Output: String ): LKProof = {
    val resProof = reconstructRobinsonProofFromOutput( p9Output )
    val endSequent = withTempFile.fromString( p9Output ) { p9File =>
      val tptpEndSequent = InferenceExtractor.viaLADR( p9File )
      if ( containsStrongQuantifier( tptpEndSequent ) ) {
        // in this case the prover9 proof contains skolem symbols which we do not try to match
        InferenceExtractor.clausesViaLADR( p9File )
      } else {
        tptpEndSequent
      }
    }

    val closure = HOLSequent(
      endSequent.antecedent.map( x => univclosure( x ) ),
      endSequent.succedent.map( x => existsclosure( x ) )
    )

    val ourCNF = CNFn.toFClauseList( endSequent.toFormula )

    val fixedResProof = fixDerivation( resProof, ourCNF )

    RobinsonToLK( fixedResProof, closure )
  }

  private def withRenamedConstants( cnf: List[HOLClause] )( f: ( Map[Const, String], List[HOLClause] ) => Option[RobinsonResolutionProof] ): Option[RobinsonResolutionProof] = {
    val ( renamedCNF, renaming, invertRenaming ) = renameConstantsToFi( cnf )
    f( renaming, renamedCNF ) map { renamedProof =>
      NameReplacement( renamedProof, invertRenaming )
    }
  }

  private def withGroundVariables( seq: HOLSequent )( f: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    val ( renamedSeq, invertRenaming ) = groundFreeVariables( seq )
    f( renamedSeq ) map { renamedProof =>
      applyReplacement( renamedProof, invertRenaming )._1
    }
  }

  def toP9Input( cnf: List[HOLClause], renaming: Map[Const, String] ): String = {
    val commands = ArrayBuffer[String]()

    commands += "set(quiet)" // suppresses noisy output on stderr
    commands += "clear(auto_denials)" // prevents prover9 from exiting with error code 2 even though a proof was found
    commands ++= extraCommands( renaming )

    commands += "formulas(sos)"
    commands ++= cnf map toP9Input
    commands += "end_of_list"

    commands.map( _ + ".\n" ).mkString
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