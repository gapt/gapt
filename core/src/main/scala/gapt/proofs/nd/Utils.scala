package gapt.proofs.nd

import gapt.expr.Var
import gapt.expr.util.freeVariables

object freeVariablesND {
  def apply( p: NDProof ): Set[Var] = p match {
    case ExistsElimRule( leftSubProof, rightSubProof, _, eigenVariable ) =>
      freeVariables( p.conclusion ) ++ apply( leftSubProof ) ++ apply( rightSubProof ) - eigenVariable
    case ForallIntroRule( subProof, eigenVariable, _ ) =>
      apply( subProof ) - eigenVariable
    case InductionRule( cases, main, term ) =>
      freeVariables( p.conclusion ) ++ ( cases flatMap { c =>
        apply( c.proof ) -- c.eigenVars
      } )
    case _ =>
      freeVariables( p.conclusion ) ++ p.immediateSubProofs.flatMap( apply )
  }
}