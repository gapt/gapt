package at.logic.gapt.provers.prover9

import java.io.{ IOException, ByteArrayInputStream, ByteArrayOutputStream }

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ existsclosure, univclosure, CNFn }
import at.logic.gapt.formats.ivy.IvyParser
import at.logic.gapt.formats.ivy.IvyParser.IvyStyleVariables
import at.logic.gapt.formats.ivy.conversion.IvyToRobinson
import at.logic.gapt.proofs.lk.base.{ LKProof, FSequent }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.robinson.RobinsonResolutionProof
import at.logic.gapt.provers.prover9.commands.InferenceExtractor
import at.logic.gapt.provers.{ renameConstantsToFi, Prover }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.io.Source
import scala.sys.process._

class Prover9ProverV2 extends Prover with ExternalProgram {
  override def getLKProof( seq: FSequent ): Option[LKProof] =
    getRobinsonProof( seq ) map { robinsonProof =>
      RobinsonToLK( robinsonProof, seq )
    }

  override def isValid( seq: FSequent ): Boolean =
    getRobinsonProof( seq ).isDefined

  def getRobinsonProof( seq: FSequent ): Option[RobinsonResolutionProof] =
    withRenamedConstants( seq ) { seq =>
      val cnf = CNFn.toFClauseList( seq.toFormula ).map( renameVars )

      val p9Input = toP9Input( cnf )
      withTempFile.fromString( p9Input ) { p9InputFile =>
        try Some( Seq( "prover9", "-f", p9InputFile ) !! )
        catch {
          case e: RuntimeException => None
        }
      } map { p9Output => parseProof( p9Output ) }
    }

  def parseProof( content: String ) = {
    // TODO: this will probably break like veriT before...
    val ivy = "prooftrans ivy" #< new ByteArrayInputStream( content.getBytes ) !!

    val ivyProof = withTempFile.fromString( ivy ) { ivyFile => IvyParser( ivyFile, IvyStyleVariables ) }

    IvyToRobinson( ivyProof )
  }

  def reconstructLKProofFromFile( p9File: String ): LKProof =
    reconstructLKProofFromOutput( Source.fromFile( p9File ).mkString )

  def reconstructLKProofFromOutput( p9Output: String ): LKProof = {
    // The TPTP prover9 output files can't be read by prooftrans ivy directly...
    val fixedP9Output = "prooftrans" #< new ByteArrayInputStream( p9Output.getBytes() ) !!

    val resProof = parseProof( fixedP9Output )
    val endSequent = withTempFile.fromString( p9Output ) { p9File =>
      InferenceExtractor.viaLADR( p9File )
    }

    val closure = FSequent( endSequent.antecedent.map( x => univclosure( x ) ),
      endSequent.succedent.map( x => existsclosure( x ) ) )

    val ourCNF = CNFn.toFClauseList( endSequent.toFormula )

    val fixedResProof = fixDerivation( resProof, ourCNF.map( _.toFSequent ) )

    RobinsonToLK( fixedResProof, closure )
  }

  def renameVars( clause: FClause ): FClause =
    Substitution( freeVariables( clause.toFSequent.toFormula ).
      toSeq.zipWithIndex.map {
        case ( v, i ) => v -> FOLVar( s"x$i" )
      } )( clause )

  private def withRenamedConstants( seq: FSequent )( f: FSequent => Option[RobinsonResolutionProof] ): Option[RobinsonResolutionProof] = {
    val ( renamedSeq, invertRenaming ) = renameConstantsToFi( seq )
    f( renamedSeq ) map { renamedProof =>
      NameReplacement( renamedProof, invertRenaming )
    }
  }

  def toP9Input( cnf: List[FClause] ): String =
    ( "set(quiet)" +: "formulas(sos)" +: cnf.map( toP9Input ) :+ "end_of_list" ).map( _ + ".\n" ).mkString
  def toP9Input( clause: FClause ): String = toP9Input( clause.toFSequent.toFormula )
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

