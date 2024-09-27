package gapt.proofs.lk.transformations

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ExchangeLeftMacroRule
import gapt.proofs.lk.rules.macros.ExchangeRightMacroRule

/**
 * Eliminates definitions from a lambda expression, HOL formula, or LK proof.
 */
object eliminateDefinitions {

  /**
   * Creates a new `eliminateDefinitions` object.
   * @param dmap The definitions to be eliminated.
   */
  def apply(dmap: Map[_ <: Const, _ <: Expr]): eliminateDefinitions =
    new eliminateDefinitions(Normalizer(dmap.map[ReductionRule](ReductionRule.apply)))

  /**
   * Given an implicit [[gapt.proofs.context.Context]] in scope, this removes all definitions in that context from a
   * proof.
   * @param proof The proof to be transformed.
   * @param ctx An implicit context. Definitions in this will be removed from proof.
   */
  def apply(proof: LKProof)(implicit ctx: Context): LKProof =
    apply(proof, ctx.normalizer)

  def apply(proof: LKProof, normalizer: Normalizer): LKProof =
    new eliminateDefinitions(normalizer).apply(proof)
}

/**
 * Implements definition elimination.
 */
class eliminateDefinitions private (normalizer: Normalizer) extends Function[Expr, Expr] {
  def apply(e: Expr): Expr = normalizer.normalize(e)
  def apply(f: Formula): Formula = apply(f: Expr).asInstanceOf[Formula]

  def apply(proof: LKProof): LKProof = proof match {
    // introductory rules
    case LogicalAxiom(atom) => LogicalAxiom(apply(atom))

    case TopAxiom    => TopAxiom
    case BottomAxiom => BottomAxiom

    case ReflexivityAxiom(term) => ReflexivityAxiom(apply(term))

    case ProofLink(name, seq) => ProofLink(apply(name), seq map apply)

    // structural rules
    case CutRule(leftSubProof, aux1, rightSubProof, aux2) =>
      CutRule(apply(leftSubProof), aux1, apply(rightSubProof), aux2)

    case WeakeningLeftRule(subProof, main) =>
      WeakeningLeftRule(apply(subProof), apply(main))

    case WeakeningRightRule(subProof, main) =>
      WeakeningRightRule(apply(subProof), apply(main))

    case ContractionLeftRule(subProof, aux1, aux2) =>
      ContractionLeftRule(apply(subProof), aux1, aux2)

    case ContractionRightRule(subProof, aux1, aux2) =>
      ContractionRightRule(apply(subProof), aux1, aux2)

    // logical rules
    case NegLeftRule(subProof, aux) =>
      NegLeftRule(apply(subProof), aux)

    case NegRightRule(subProof, aux) =>
      NegRightRule(apply(subProof), aux)

    case AndLeftRule(subProof, aux1, aux2) =>
      AndLeftRule(apply(subProof), aux1, aux2)

    case AndRightRule(leftSubProof, aux1, rightSubProof, aux2) =>
      AndRightRule(apply(leftSubProof), aux1, apply(rightSubProof), aux2)

    case OrRightRule(subProof, aux1, aux2) =>
      OrRightRule(apply(subProof), aux1, aux2)

    case OrLeftRule(leftSubProof, aux1, rightSubProof, aux2) =>
      OrLeftRule(apply(leftSubProof), aux1, apply(rightSubProof), aux2)

    case ImpLeftRule(leftSubProof, aux1, rightSubProof, aux2) =>
      ImpLeftRule(apply(leftSubProof), aux1, apply(rightSubProof), aux2)

    case ImpRightRule(subProof, aux1, aux2) =>
      ImpRightRule(apply(subProof), aux1, aux2)

    // quantfication rules
    case ForallLeftRule(subProof, aux, f, term, quant) =>
      ForallLeftRule(apply(subProof), aux, apply(f), apply(term), quant)

    case ExistsRightRule(subProof, aux, f, term, quant) =>
      ExistsRightRule(apply(subProof), aux, apply(f), apply(term), quant)

    case ExistsLeftRule(subProof, aux, eigen, quant) =>
      ExistsLeftRule(apply(subProof), aux, eigen, quant)

    case ForallRightRule(subProof, aux, eigen, quant) =>
      ForallRightRule(apply(subProof), aux, eigen, quant)

    case ExistsSkLeftRule(subProof, aux, main, skT) =>
      ExistsSkLeftRule(apply(subProof), aux, apply(main), apply(skT))

    case ForallSkRightRule(subProof, aux, main, skT) =>
      ForallSkRightRule(apply(subProof), aux, apply(main), apply(skT))

    // equational rules
    case proof @ EqualityLeftRule(subProof, eq, aux, con) =>
      EqualityLeftRule(apply(subProof), eq, aux, apply(con).asInstanceOf[Abs])

    case proof @ EqualityRightRule(subProof, eq, aux, con) =>
      EqualityRightRule(apply(subProof), eq, aux, apply(con).asInstanceOf[Abs])

    /* The cases for definition rules employ a trick: The removal of the rule would change the order of the end
        sequent. We use exchange macro rules to artificially replicate the movement of formulas that the definition
         rule would have performed.*/

    case proof @ ConversionLeftRule(subProof, aux, _) =>
      if (apply(proof.auxFormula) == apply(proof.mainFormula))
        ExchangeLeftMacroRule(apply(subProof), aux)
      else
        ConversionLeftRule(apply(subProof), aux, apply(proof.mainFormula))

    case proof @ ConversionRightRule(subProof, aux, _) =>
      if (apply(proof.auxFormula) == apply(proof.mainFormula))
        ExchangeRightMacroRule(apply(subProof), aux)
      else
        ConversionRightRule(apply(subProof), aux, apply(proof.mainFormula))

    case InductionRule(cases, main, term) =>
      InductionRule(cases map { cs => cs.copy(proof = apply(cs.proof)) }, apply(main).asInstanceOf[Abs], apply(term))
  }
}
