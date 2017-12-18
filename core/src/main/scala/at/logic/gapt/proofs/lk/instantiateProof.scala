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
  def Instantiate( proofName: Expr )( implicit ctx: Context ): LKProof = regularize( eliminateDefinitions( instantiateProof( proofName )( ctx ) ) )

  def apply( proofName: Expr )( implicit ctx: Context ): LKProof = withConnector( proofName )._2

  /**
   * Given a proof name, returns a maximally instantiated proof.
   *
   * @return Connector from instantiated proof to the declared sequent of the proof name,
   *         together with the instantiated proof
   */
  def withConnector( proofName: Expr )( implicit ctx: Context ): ( SequentConnector, LKProof ) = {
    ctx.get[Context.ProofDefinitions].findWithConnector(proofName).headOption match {
      case Some((connLink2DefPrf, subst, defPrf)) =>
        val (instPrf, connInstPrf2SubstDefPrf) = buildProof.withSequentConnector(subst(defPrf), ctx)
        connInstPrf2SubstDefPrf * connLink2DefPrf.inv -> instPrf
      case None =>
        val Some(sequent) = ctx.get[Context.ProofNames].lookup(proofName)
        SequentConnector(sequent) -> ProofLink(proofName, sequent)
    }
  }
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    buildProof( proof, ctx )

  private object buildProof extends LKVisitor[Context] {
    override def visitProofLink( link: ProofLink, otherArg: Context ): ( LKProof, SequentConnector ) = {
      val ( connInstProof2Link, instProof ) = instantiateProof.withConnector( link.referencedProof )( otherArg )
      ( instProof, connInstProof2Link )
    }
  }

}
