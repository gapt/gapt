package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.existentialClosure
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.{ HOLClause, Sequent, FOLClause }
import at.logic.gapt.proofs.expansion.InstanceTermEncoding

object extractRecSchemFromResProof {
  def apply( p: ResolutionProof ): ( RecursionScheme, InstanceTermEncoding ) = ???

  def apply( root: ResolutionProof, clauseTerm: HOLClause => Option[LambdaExpression] ): RecursionScheme = ???
}