package gapt.proofs.lk.util

import gapt.expr.Expr
import gapt.proofs.SequentConnector
import gapt.proofs.SequentConnector.guessInjection
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofDefinitions
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.macros.WeakeningMacroRule
import gapt.proofs.lk.transformations.eliminateDefinitions

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
  def Instantiate( proofName: Expr )( implicit ctx: Context ): LKProof = regularize( eliminateDefinitions( instantiateProof( proofName )( ctx ) ) )

  def apply( proofName: Expr )( implicit ctx: Context ): LKProof = withConnector( proofName )._2

  /**
   * Given a proof name, returns a maximally instantiated proof.
   *
   * @return Connector from instantiated proof to the declared sequent of the proof name,
   *         together with the instantiated proof
   */
  def withConnector( proofName: Expr )( implicit ctx: Context ): ( SequentConnector, LKProof ) = {
    ctx.get[ProofDefinitions].findWithConnector( proofName ).headOption match {
      case Some( ( connDefPrf2Link, subst, defPrf ) ) =>
        val ( instPrf, connInstPrf2SubstDefPrf ) = buildProof.withSequentConnector( subst( defPrf ), ctx )
        connInstPrf2SubstDefPrf * connDefPrf2Link -> instPrf
      case None =>
        val Some( sequent ) = ctx.get[ProofNames].lookup( proofName )
        SequentConnector( sequent ) -> ProofLink( proofName, sequent )
    }
  }
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    buildProof( proof, ctx )

  private object buildProof extends LKVisitor[Context] {
    override def visitProofLink( link: ProofLink, otherArg: Context ): ( LKProof, SequentConnector ) = {
      val ( _, instProof ) = instantiateProof.withConnector( link.referencedProof )( otherArg )
      val finProof = WeakeningMacroRule( instProof, link.referencedSequent )
      ( finProof, guessInjection( finProof.endSequent, link.referencedSequent ) )
    }
  }

}
