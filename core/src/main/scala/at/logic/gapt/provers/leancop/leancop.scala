package at.logic.gapt.provers.leancop

import java.io.{ IOException, StringReader }

import at.logic.gapt.expr.{ All, Eq, Substitution, TermReplacement }
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.formats.leancop.LeanCoPParser
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.{ Context, HOLClause, HOLSequent, MutableContext, Sequent }
import at.logic.gapt.proofs.expansion.{ ETWeakQuantifierBlock, ExpansionProof, ExpansionProofToLK, ExpansionSequent }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution.{ ResolutionToExpansionProof, expansionProofFromInstances, structuralCNF }
import at.logic.gapt.provers.{ OneShotProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, Maybe, runProcess, withTempFile }
import at.logic.gapt.utils.EitherHelpers._

object LeanCoP extends LeanCoP
class LeanCoP extends OneShotProver with ExternalProgram {
  private val nLine = sys.props( "line.separator" )

  override def isValid( s: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
    getExpansionProof( s )( ctx.map( _.newMutable ) ).isDefined

  override def getExpansionProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
    val cnf = structuralCNF( s ).map( c => universalClosure( c.conclusion.toDisjunction ) -> c ).toMap
    // LeanCoP doesn't like empty clauses
    for ( ( _, clause ) <- cnf if clause.isProof ) return Some( ResolutionToExpansionProof( clause ) )

    renameConstantsToFi.wrap( cnf.keys ++: Sequent() )( ( renaming, sequent: HOLSequent ) => {
      val tptp = TPTPFOLExporter( sequent ).toString
      withTempFile.fromString( tptp ) { leanCoPInput =>
        runProcess.withExitValue( Seq( "leancop", leanCoPInput.toString ) )
      } match {
        case ( 1, leanCopOutput ) if leanCopOutput contains "is Satisfiable" =>
          None
        case ( 0, leanCopOutput ) =>
          // extract the part between the %----- delimiters
          val tptpProof = leanCopOutput.split( nLine ).
            dropWhile( !_.startsWith( "%-" ) ).drop( 1 ).
            takeWhile( !_.startsWith( "%-" ) ).
            mkString( nLine )

          LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) )
      }
    } ) map { es =>
      val hasEquality = cnf.values.flatMap( _.conclusion.elements ).exists {
        case Eq( _, _ ) => true
        case _          => false
      }

      val substs = for {
        ETWeakQuantifierBlock( shallow, _, insts ) <- es.elements
        ( formula @ All.Block( vars, _ ), clause ) <- cnf
        if formula == shallow
      } yield clause.conclusion.asInstanceOf[HOLClause] ->
        insts.keys.map( s => Substitution( vars zip s ) ).toSet

      expansionProofFromInstances( substs.toMap, cnf.values.toSet, !hasEquality )
    }
  }

  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
    getExpansionProof( seq ) map { ExpansionProofToLK( _ ).get }

  override val isInstalled: Boolean = try runProcess.withExitValue( Seq( "leancop" ) )._1 == 2
  catch { case _: IOException => false }
}
