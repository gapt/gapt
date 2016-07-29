package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.HOLSequent

object mapInputClauses {

  def apply( proof: ResolutionProof )( f: HOLSequent => ResolutionProof ): ResolutionProof =
    new ResolutionProofVisitor {
      override def visitInput( p: Input ): ResolutionProof = f( p.sequent )
    }.apply( proof )
}
