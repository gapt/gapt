package gapt.proofs.lk.rules.macros

import gapt.expr.Const
import gapt.expr.TermReplacement
import gapt.expr.containedNames
import gapt.expr.formula.Atom
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.lkProofReplaceable
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.transformations.cleanCuts
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot

object FOTheoryMacroRule {
  def apply(sequent: HOLSequent, prover: ResolutionProver = Escargot)(implicit ctx: Context): LKProof =
    option(sequent, prover).getOrElse {
      throw new IllegalArgumentException(s"Cannot prove $sequent in:\n$ctx")
    }
  def option(sequent: HOLSequent, prover: ResolutionProver = Escargot)(implicit ctx: Context): Option[LKProof] = {
    import gapt.proofs.resolution._
    // FIXME: this also includes defined proofs
    val axioms = ctx.get[ProofNames].sequents.filter(_.forall(_.isInstanceOf[Atom])).toSet
    val nameGen = rename.awayFrom(containedNames(axioms + sequent))
    val grounding = freeVariables(sequent).map(v => v -> Const(nameGen.fresh(v.name), v.ty))
    val cnf = axioms ++ Substitution(grounding)(sequent).map(Sequent() :+ _, _ +: Sequent()).elements
    prover.getResolutionProof(cnf.map(Input.apply)) map { p =>
      var lk = ResolutionToLKProof(
        eliminateSplitting(p),
        {
          i =>
            (i: @unchecked) match {
              case Input(seq) if axioms.contains(seq) =>
                ProofLink(ctx.get[ProofNames].find(seq).get)
              case Input(unit) if unit.size == 1 => LogicalAxiom(unit.elements.head)
            }
        }
      )
      lk = TermReplacement.hygienic(lk, grounding.map(_.swap).toMap)
      lk = cleanCuts(lk)
      lk
    }
  }
}
