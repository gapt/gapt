package at.logic.gapt.proofs.lk
import at.logic.gapt.expr._
import at.logic.gapt.proofs._

object instantiateProof {
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
    eliminateDefinitions( instantiateProof( proofName )( ctx ) )

  def apply( proofName: Expr )( implicit ctx: Context ): LKProof =
    ctx.get[Context.ProofDefinitions].find( proofName ) match {
      case Some( ( defPrf, subst ) ) => apply( subst( defPrf ) )
      case None => {
        ProofLink( proofName, ctx.get[Context.ProofNames].lookup( proofName ).get )
      }
    }
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    buildProof( proof, ctx )

  private object buildProof extends LKVisitor[Context] {
    override def visitProofLink( proof: ProofLink, otherArg: Context ): ( LKProof, SequentConnector ) = {
      val upProof = instantiateProof( proof.referencedProof )( otherArg )
      ( upProof, SequentConnector.guessInjection( upProof.endSequent, proof.conclusion ).inv )
    }
  }

}
