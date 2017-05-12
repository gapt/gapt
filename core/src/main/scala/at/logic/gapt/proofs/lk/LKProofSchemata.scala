package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{ Apps, Expr, syntacticMatching, _ }
import at.logic.gapt.proofs._

/**
 * The Point of this class is to allow the instantiation of Proof schemata.
 */
object LKProofSchemata {
  /**
   * Given a proof name found in the context and a set of arguments matching
   * the argument list of the chosen proof name this function constructs an
   * instantiation of that proof. Note that this can result in an infinite
   * loop or no proof depending on how the chosen arguments are used in the
   * the chosen proof
   *
   * @param proofName The name of the linkProof
   */
  def Instantiate( proofName: Expr )( implicit ctx: Context ): LKProof =
    ctx.get[Context.ProofDefinitions].find( proofName ).headOption match {
      case Some( ( defPrf, subst ) ) => buildProof( subst( defPrf ), ctx )
      case None                      => ProofLink( proofName, ctx.get[Context.ProofNames].lookup( proofName ).get )
    }

  object buildProof extends LKVisitor[Context] {
    override def visitProofLink( proof: ProofLink, otherArg: Context ): ( LKProof, SequentConnector ) = {
      val upProof = Instantiate( proof.referencedProof )( otherArg )
      ( upProof, SequentConnector.guessInjection( upProof.endSequent, proof.conclusion ).inv )
    }
  }

}
