package gapt.provers.leancop

import java.io.IOException
import java.io.StringReader
import gapt.expr.formula.hol.universalClosure
import gapt.expr.formula.{ All, Atom, Eq, Neg, Or }
import gapt.expr.subst.Substitution
import gapt.formats.leancop.{ LeanCoP21Parser, LeanCoPParser }
import gapt.proofs.expansion.{ ETWeakQuantifierBlock, ExpansionProof, ExpansionProofToLK, ExpansionSequent, formulaToExpansionTree }
import gapt.formats.tptp.TptpFOLExporter
import gapt.logic.{ Polarity, clauseSubsumption }
import gapt.proofs.{ Clause, HOLClause, HOLSequent, Sequent, RichFormulaSequent }
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.ResolutionToExpansionProof
import gapt.proofs.resolution.expansionProofFromInstances
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.OneShotProver
import gapt.provers.renameConstantsToFi
import gapt.utils.EitherHelpers._
import gapt.utils.ExternalProgram
import gapt.utils.Maybe
import gapt.utils.runProcess
import gapt.utils.withTempFile

object LeanCoP extends LeanCoP
class LeanCoP extends OneShotProver with ExternalProgram {
  private val nLine = sys.props( "line.separator" )

  override def isValid( s: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
    getExpansionProof( s )( ctx.map( _.newMutable ) ).isDefined

  override def getExpansionProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = scala.util.boundary {
    val cnf = structuralCNF( s ).map( c => universalClosure( c.conclusion.toDisjunction ) -> c ).toMap
    // LeanCoP doesn't like empty clauses
    for ( ( _, clause ) <- cnf if clause.isProof ) scala.util.boundary.break(Some( ResolutionToExpansionProof( clause ) ))

    renameConstantsToFi.wrap( cnf.keys ++: Sequent() )( ( renaming, sequent: HOLSequent ) => {
      val tptp = TptpFOLExporter( sequent ).toString
      val ( exitValue, stdout ) = withTempFile.fromString( tptp ) { leanCoPInput =>
        runProcess.withExitValue( Seq( "leancop", leanCoPInput.toString ) )
      }
      if ( exitValue == 1 && stdout.contains( "is Satisfiable" ) ) {
        None
      } else if ( exitValue == 0 ) {
        if ( stdout.contains( "%-" ) ) { // LeanCop TPTP format
          // extract the part between the %----- delimiters
          val tptpProof = stdout.split( nLine ).
            dropWhile( !_.startsWith( "%-" ) ).drop( 1 ).
            takeWhile( !_.startsWith( "%-" ) ).
            mkString( nLine )

          Some( LeanCoPParser.getExpansionProof( new StringReader( tptpProof ) ).get )
        } else { // LeanCoP 2.1 format (only compact atm)
          val Right( connPrf ) = LeanCoP21Parser.parse( stdout ): @unchecked

          val clauses = connPrf.toFOLClauses.map( _.swapped )
          Some( sequent.map {
            case fml @ All.Block( _, Or.nAry( lits ) ) =>
              val cls = Clause( lits.collect { case Neg( a: Atom ) => a }, lits.collect { case a: Atom => a } )
              formulaToExpansionTree(
                fml,
                for { inst <- clauses; subst <- clauseSubsumption( cls, inst ) } yield subst,
                Polarity.InAntecedent )
          } )
        }
      } else {
        throw new IllegalArgumentException( s"Unexpected leancop output with exit value ${exitValue}:\n${stdout}" )
      }
    } ).map {
      case es =>
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
