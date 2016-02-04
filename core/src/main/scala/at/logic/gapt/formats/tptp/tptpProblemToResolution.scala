package at.logic.gapt.formats.tptp

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.resolution.{ Input, ResolutionProof }

object tptpProblemToResolution {
  def apply( tptpFile: TptpFile ): Set[ResolutionProof] =
    tptpFile.inputs.map {
      case AnnotatedFormula( "cnf", _, _, formula, _ ) =>
        CNFp.toClauseList( formula ) match {
          case Seq( clause ) => Input( clause )
        }
      case AnnotatedFormula( _, _, "conjecture", formula, _ ) =>
        Input( formula +: Sequent() )
      case AnnotatedFormula( _, _, _, formula, _ ) =>
        Input( Sequent() :+ formula )
      case input => throw new IllegalArgumentException( input.toString )
    }.toSet

}
