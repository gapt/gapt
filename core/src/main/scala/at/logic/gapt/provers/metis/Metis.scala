package at.logic.gapt.provers.metis

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.proofs.{ FOLClause, HOLClause }
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, runProcess }

import scalaz.Success

object Metis extends Metis

class Metis extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = toTPTP( labelledCNF )
        val output = runProcess.withTempInputFile( Seq( "metis", "--show", "proof" ), tptpIn )
        val lines = output.split( "\n" ).toSeq
        if ( lines.exists( _.startsWith( "SZS status Unsatisfiable" ) ) ) {
          val tptpDerivation = lines.
            dropWhile( !_.startsWith( "SZS output start CNFRefutation " ) ).drop( 1 ).
            takeWhile( !_.startsWith( "SZS output end CNFRefutation " ) ).
            mkString( "\n" )
          RefutationSketchToResolution( TptpProofParser.parse( tptpDerivation, labelledCNF mapValues {
            Seq( _ )
          } ) ) match {
            case Success( proof ) => Some( proof )
          }
        } else if ( lines.exists( _.startsWith( "SZS status Satisfiable" ) ) ) {
          None
        } else {
          throw new IllegalArgumentException
        }
      }
    )

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
    toTPTP( renameVars( clause.toDisjunction ) )

  private def toTPTP( cnf: Map[String, FOLClause] ): String =
    cnf.map {
      case ( label, clause ) =>
        s"cnf($label, axiom, ${toTPTP( clause )})."
    }.mkString( sys.props( "line.separator" ) )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "metis", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
