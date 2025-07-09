package gapt.proofs.lk.util

import gapt.expr.Expr
import gapt.proofs.SequentConnector
import gapt.proofs.SequentConnector.guessInjection
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofDefinitions
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.LKProofSubstitutableDefault
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.macros.WeakeningMacroRule
import gapt.proofs.lk.transformations.eliminateDefinitions

object instantiateProof {

  /**
   * Given a proof name found in the context and a set of arguments matching
   * the argument list of the chosen proof name this function constructs an
   * instantiation of that proof. Note that this can result in an infinite
   * loop or no proof depending on how the chosen arguments are used in
   * the chosen proof
   *
   * @param proofName The name of the linkProof
   * @param alwaysResolve defines if proof links must be resolved (true) or
   *                      if they stay in place when they can not be resolved (false)
   */
  def Instantiate(proofName: Expr, alwaysResolve: Boolean = false)(implicit ctx: Context): LKProof = {
    val ip = if (alwaysResolve) { applyWithChecking(proofName)(ctx) } else { apply(proofName)(ctx) }
    regularize(eliminateDefinitions(ip))
  }

  def apply(proofName: Expr)(implicit ctx: Context): LKProof = withConnector(proofName)._2
  def applyWithChecking(proofName: Expr)(implicit ctx: Context): LKProof = { withConnector(proofName, true)._2 }

  /**
   * Given a proof name, returns a maximally instantiated proof.
   *
   * @return Connector from instantiated proof to the declared sequent of the proof name,
   *         together with the instantiated proof
   */
  def withConnector(proofName: Expr, alwaysResolve: Boolean = false)(implicit ctx: Context): (SequentConnector, LKProof) = {
    val bp = if (alwaysResolve) buildProofStrict else buildProof
    ctx.get[ProofDefinitions].findWithConnector(proofName).headOption match {
      case Some((connDefPrf2Link, subst, defPrf)) =>
        val (instPrf, connInstPrf2SubstDefPrf) = bp.withSequentConnector(subst(defPrf), ctx)
        connInstPrf2SubstDefPrf * connDefPrf2Link -> instPrf
      case None if !alwaysResolve =>
        val Some(sequent) = ctx.get[ProofNames].lookup(proofName): @unchecked
        SequentConnector(sequent) -> ProofLink(proofName, sequent)
      case None /* if alwaysResolve */ =>
        throw new Exception(s"Proof linking failed for ${proofName}, possible proof definitions are:\n${ctx.get[ProofNames]}")
    }
  }

  def apply(proof: LKProof)(implicit ctx: Context): LKProof = buildProof(proof, ctx)
  def applyWithChecking(proof: LKProof)(implicit ctx: Context): LKProof = buildProofStrict(proof, ctx)

  private class buildProof(strict: Boolean) extends LKVisitor[Context] {
    override def visitProofLink(link: ProofLink, otherArg: Context): (LKProof, SequentConnector) = {
      val (_, instProof) = instantiateProof.withConnector(link.referencedProof, strict)(otherArg)
      val finProof = WeakeningMacroRule(instProof, link.referencedSequent)
      (finProof, guessInjection(finProof.endSequent, link.referencedSequent))
    }
  }

  private object buildProof extends buildProof(false)
  private object buildProofStrict extends buildProof(true)

}
