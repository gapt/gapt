package gapt.proofs.lk.util

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.hol.instantiate
import gapt.expr.subst.Substitution
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.SequentConnector
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.LKProofSubstitutableDefault
import gapt.proofs.lk.lkProofReplaceable
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.StrongQuantifierRule
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.provers.viper.aip
import gapt.utils.NameGenerator

object containsEqualityReasoning {

  /**
   * @param proof An LKProof.
   * @return true iff this proof contains a reflexivity axiom or an equational inference
   */
  def apply(proof: LKProof): Boolean =
    proof.subProofs.exists {
      case ReflexivityAxiom(_)           => true
      case EqualityLeftRule(_, _, _, _)  => true
      case EqualityRightRule(_, _, _, _) => true
      case _                             => false
    }
}

object containsDefinitionRules {
  def apply(proof: LKProof): Boolean =
    proof.subProofs.exists {
      case ConversionLeftRule(_, _, _) | ConversionRightRule(_, _, _) => true
      case _                                                          => false
    }
}

object EigenVariablesLK {
  def apply(p: LKProof): Set[Var] = p match {
    case StrongQuantifierRule(subProof, _, eigen, _, _) =>
      apply(subProof) ++ Set(eigen)
    case InductionRule(cases, _, _) =>
      cases.flatMap { c => c.eigenVars }.toSet ++
        (cases flatMap { c => apply(c.proof) })
    case _ =>
      p.immediateSubProofs.flatMap(apply).toSet
  }
}

object freeVariablesLK {
  def apply(p: LKProof): Set[Var] = p match {
    case StrongQuantifierRule(subProof, _, eigen, _, _) =>
      apply(subProof) - eigen
    case InductionRule(cases, _, term) =>
      freeVariables(p.conclusion) ++ freeVariables(term) ++ (cases flatMap { c =>
        apply(c.proof) -- c.eigenVars
      })
    case _ =>
      freeVariables(p.conclusion) ++ p.immediateSubProofs.flatMap(apply)
  }
}

object groundFreeVarsLK {
  def getMap(p: LKProof): Set[(Var, Const)] = {
    val nameGen = rename.awayFrom(containedNames(p))
    for (v @ Var(n, t) <- freeVariablesLK(p)) yield v -> Const(nameGen fresh n, t)
  }

  def apply(p: LKProof): LKProof = Substitution(getMap(p))(p)

  def wrap[I, O](p: LKProof)(f: LKProof => I)(implicit ev: Replaceable[I, O]): O = {
    val grounding = getMap(p)
    TermReplacement.hygienic(f(Substitution(grounding)(p)), grounding.map(_.swap).toMap)
  }
}

object cutFormulas {
  def apply(proof: LKProof) = proof.treeLike.postOrder.flatMap({
    case CutRule(p, o, _, _) => List(p.conclusion(o))
    case _                   => List()
  }).toSet
}

object isRegular {

  /**
   * Tests for regularity by checking whether all eigenvariables are distinct.
   *
   * @param proof An LKProof.
   * @return true iff proof is regular.
   */
  def apply(proof: LKProof): Boolean = {
    val eigenvariables: Seq[Var] = proof.subProofs.toSeq flatMap {
      case ExistsLeftRule(_, _, eigenvariable, _)  => Seq(eigenvariable)
      case ForallRightRule(_, _, eigenvariable, _) => Seq(eigenvariable)
      case InductionRule(inductionCases, _, _) =>
        inductionCases flatMap { _.eigenVars }
      case _ => Seq()
    }
    eigenvariables == eigenvariables.distinct
  }
}

/**
 * Proof regularization
 *
 */
object regularize {

  /**
   * Renames all eigenvariables in a proof so that it becomes regular.
   *
   * @param proof An LKProof.
   * @return A regular LKProof.
   */
  def apply(proof: LKProof): LKProof =
    new Regularize(rename.awayFrom(freeVariablesLK(proof))).apply(proof, ())

  private class Regularize(nameGen: NameGenerator) extends LKVisitor[Unit] {

    protected override def visitForallRight(proof: ForallRightRule, arg: Unit) = {
      val ForallRightRule(subProof, aux, eigen, quant) = proof
      val eigenNew = nameGen.fresh(eigen)
      val (subProofNew, subConnector) = recurse(Substitution(eigen -> eigenNew)(subProof), ())
      val proofNew = ForallRightRule(subProofNew, aux, eigenNew, quant)
      (proofNew, proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv)
    }

    protected override def visitExistsLeft(proof: ExistsLeftRule, arg: Unit) = {
      val ExistsLeftRule(subProof, aux, eigen, quant) = proof
      val eigenNew = nameGen.fresh(eigen)
      val (subProofNew, subConnector) = recurse(Substitution(eigen -> eigenNew)(subProof), ())
      val proofNew = ExistsLeftRule(subProofNew, aux, eigenNew, quant)
      (proofNew, proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv)
    }

    protected override def visitInduction(proof: InductionRule, arg: Unit) = {
      val InductionRule(cases, _, term) = proof

      val newQuant = nameGen.fresh(proof.quant)

      val newCasesConnectors = cases map { c =>
        val renaming = for (ev <- c.eigenVars) yield ev -> nameGen.fresh(ev)
        val (subProofNew, subConnector) = recurse(Substitution(renaming)(c.proof), ())
        c.copy(proof = subProofNew, eigenVars = c.eigenVars map renaming.toMap) -> subConnector
      }

      val (casesNew, subConnectors) = newCasesConnectors.unzip
      val proofNew = InductionRule(casesNew, proof.formula, term)
      val subConnectors_ = for ((c1, c2, c3) <- proofNew.occConnectors.lazyZip(subConnectors).lazyZip(proof.occConnectors)) yield c1 * c2 * c3.inv
      val connector = if (subConnectors_.isEmpty) SequentConnector(proofNew.endSequent) else subConnectors_.reduceLeft(_ + _)

      (proofNew, connector)
    }
  }
}

object extractInductionAxioms {

  /**
   * Extracts all the inductions axioms from a proof.
   *
   * @param proof The proof from which induction axioms are to be extracted.
   * @param ctx Defines constants, types, etc.
   * @return A list of all induction axioms that represent the induction inferences that occur in the
   *         proof. Note that the induction axioms are universally quantified if their corresponding
   *         induction inference contains free variables that occur as eigenvariables in an inference
   *         below the induction.
   */
  def apply(proof: LKProof)(implicit ctx: Context): Seq[Formula] = {
    val regularProof = regularize(proof)
    extractAxioms(regularProof, EigenVariablesLK(regularProof))
  }

  /**
   * Extracts induction axioms from a regular proof.
   * @param proof A regular proof, see [[extractInductionAxioms.apply]].
   * @param eigenVariables The set of eigenvariables of the proof.
   * @param ctx see [[extractInductionAxioms.apply]].
   * @return see [[extractInductionAxioms.apply]].
   */
  private def extractAxioms(
      proof: LKProof,
      eigenVariables: Set[Var]
  )(implicit ctx: Context): Seq[Formula] = {
    proof match {
      case InductionRule(inductionCases, inductionFormula, _) =>
        val axiom = inductionAxiom(inductionFormula)
        All.Block(
          freeVariables(axiom).filter { eigenVariables.contains(_) }.toSeq,
          axiom
        ) +: inductionCases.flatMap { ic => extractAxioms(ic.proof, eigenVariables) }
      case _ => proof.immediateSubProofs.flatMap { extractAxioms(_, eigenVariables) }
    }
  }

  /**
   * Creates a standard induction axiom.
   *
   * @param abstraction The abstraction on which induction is carried out. The abstracted variable must
   *                    be of inductive type and the lambda expression must be a formula.
   * @param ctx Defines the constants, types, etc.
   * @return A standard induction axiom for the given formula.
   */
  private def inductionAxiom(abstraction: Abs)(implicit ctx: Context): Formula = {
    val Abs(variable, formula) = abstraction
    val constructors = aip.getConstructors(variable.ty.asInstanceOf[TBase], ctx).toOption.get
    aip.axioms.inductionAxiom(variable, formula.asInstanceOf[Formula], constructors)
  }
}

object instanceProof {
  def apply(proof: LKProof, terms: Expr*)(implicit dummyImplicit: DummyImplicit): LKProof =
    apply(proof, terms)

  def apply(proof: LKProof, terms: Seq[Expr]): LKProof = {
    val instantiationFormula = proof.endSequent.succedent.head
    CutRule(proof, instantiationProof(instantiationFormula, terms), instantiationFormula)
  }

  private def instantiationProof(formula: Formula, terms: Seq[Expr]): LKProof = {
    val instanceFormula = instantiate(formula, terms)
    ForallLeftBlock(LogicalAxiom(instanceFormula), formula, terms)
  }
}

object inductionEigenvariables {

  /**
   * Retrieves all of the eigenvariables of a given induction rule.
   * @param induction The induction rule.
   * @return All the eigenvariables of the induction rule.
   */
  def apply(induction: InductionRule) =
    induction.cases.flatMap(_.eigenVars).toSet
}

object logicalComplexity {
  def apply(formula: FOLFormula): Int = {
    formula match {
      case PropAtom(_) | FOLAtom(_, _) => 0
      case All(_, subformula)          => 1 + logicalComplexity(subformula)
      case Ex(_, subformula)           => 1 + logicalComplexity(subformula)
      case And(f1, f2)                 => 1 + logicalComplexity(f1) + logicalComplexity(f2)
      case Or(f1, f2)                  => 1 + logicalComplexity(f1) + logicalComplexity(f2)
      case Imp(f1, f2)                 => 1 + logicalComplexity(f1) + logicalComplexity(f2)
      case Neg(f1)                     => 1 + logicalComplexity(f1)
    }
  }

  private object PropAtom {
    def unapply(arg: Formula): Option[String] = {
      arg match {
        case Const(sym, To, _) => Some(sym)
        case _                 => None
      }
    }
  }
}

object isCutFree {

  /**
   * This method checks whether a proof is cut-free.
   * @param proof The proof to check for cut-freeness.
   * @return true if proof does not contain the cut rule, false otherwise.
   */
  def apply(proof: LKProof): Boolean =
    !proof.subProofs.exists {
      case CutRule(_, _, _, _) => true
      case _                   => false
    }

}

object isInductionFree {

  /**
   * Checks whether a proof contains induction inferences.
   * @param proof The proof to be checked.
   * @return true if the proof does not contain induction inferences, false otherwise.
   */
  def apply(proof: LKProof): Boolean =
    !proof.subProofs.exists {
      case InductionRule(_, _, _) => true
      case _                      => false
    }
}
