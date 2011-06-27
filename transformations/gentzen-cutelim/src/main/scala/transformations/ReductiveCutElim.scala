/*
 * ReductiveCutElim.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations

import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.base._
import at.logic.language.hol._
import at.logic.calculi.occurrences._
import java.lang.Exception

class ReductiveCutElimException(msg: String) extends Exception(msg)

object ReductiveCutElim {
   /*
 // Cvetan adviced to add this:
 // implicit val pointFac = at.logic.calculi.occurrences.PointerFOFactoryInstance

  def cutElim(proof: LKProof): LKProof = proof match {
    case Axiom(_) => proof
    case WeakeningLeftRule(up, _, pf) => WeakeningLeftRule.createDefault(cutElim(up), pf.formula)
    case WeakeningRightRule(up, _, pf) => WeakeningRightRule.createDefault(cutElim(up), pf.formula)
    case ContractionLeftRule(up, _, aux1, aux2, _) => ContractionLeftRule(cutElim(up), aux1, aux2)
    case ContractionRightRule(up, _, aux1, aux2, _) => ContractionRightRule(cutElim(up), aux1, aux2)
    case AndRightRule(up1, up2, _, aux1, aux2, _) => AndRightRule(cutElim(up1), cutElim(up2), aux1, aux2)
    case AndLeft1Rule(up, _, aux, prin) => prin.formula match {
      case And(aux.formula, f) => AndLeft1Rule(cutElim(up), aux, f)
    }
    case AndLeft2Rule(up, _, aux, prin) => prin.formula match {
      case And(f, aux.formula) => AndLeft2Rule(cutElim(up), f, aux)
    }
    case OrLeftRule(up1, up2, _, aux1, aux2, _) => OrLeftRule(cutElim(up1), cutElim(up2), aux1, aux2)
    case OrRight1Rule(up, _, aux, prin) => prin.formula match {
      case Or(aux.formula, f) => OrRight1Rule(cutElim(up), aux, f)
    }
    case OrRight2Rule(up, _, aux, prin) => prin.formula match {
      case Or(f, aux.formula) => OrRight2Rule(cutElim(up), f, aux)
    }
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) => ImpLeftRule(cutElim(up1), cutElim(up2), aux1, aux2)
    case ImpRightRule(up, _, aux1, aux2, _) => ImpRightRule(cutElim(up), aux1, aux2)
    case NegLeftRule(up, _, aux, _) => NegLeftRule(cutElim(up), aux)
    case NegRightRule(up, _, aux, _) => NegRightRule(cutElim(up), aux)
    case ForallLeftRule(up, _, aux, prin, subst) => ForallLeftRule(cutElim(up), aux.formula, prin.formula, subst)
    case ForallRightRule(up, _, aux, prin, eigenVar) => ForallRightRule(cutElim(up), aux.formula, prin.formula, eigenVar)
    case ExistsLeftRule(up, _, aux, prin, eigenVar) => ExistsLeftRule(cutElim(up), aux.formula, prin.formula, eigenVar)
    case ExistsRightRule(up, _, aux, prin, subst) => ExistsRightRule(cutElim(up), aux.formula, prin.formula, subst)
    case CutRule(up1, up2, _, a1, a2) => cutElim(reduceCut(up1, up2, a1.formula, a2.formula))
  }

  def reduceCut(left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula): LKProof =
    reduceGrade(left, right, cutFormula1, cutFormula2)

    // Grade reduction rules:
  private def reduceGrade(left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula): LKProof =
    (left, right) match {
    case (AndRightRule(up1, up2, _, aux1, aux2, prin1), AndLeft1Rule(up, _, aux, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        var tmp: LKProof = CutRule(up1, up, aux1, aux)
        for (i <- up2.root.antecedent) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
        for (i <- up2.root.succedent) if (i != aux2) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
        tmp
    case (AndRightRule(up1, up2, _, aux1, aux2, prin1), AndLeft2Rule(up, _, aux, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        var tmp: LKProof = CutRule(up2, up, aux2, aux)
        for (i <- up1.root.antecedent) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
        for (i <- up1.root.succedent) if (i != aux1) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
        tmp
    case (OrRight1Rule(up, _, aux, prin1), OrLeftRule(up1, up2, _, aux1, aux2, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        var tmp: LKProof = CutRule(up, up1, aux, aux1)
        for (i <- up2.root.antecedent) if (i != aux2) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
        for (i <- up2.root.succedent) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
        tmp
    case (OrRight2Rule(up, _, aux, prin1), OrLeftRule(up1, up2, _, aux1, aux2, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        var tmp: LKProof = CutRule(up, up2, aux, aux2)
        for (i <- up1.root.antecedent) if (i != aux1) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
        for (i <- up1.root.succedent) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
        tmp
    case (ImpRightRule(up, _, auxl, auxr, prin1), ImpLeftRule(up1, up2, _, aux1, aux2, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        CutRule(up1, CutRule(up, up2, auxr, aux2), aux1.formula)
    case (NegRightRule(upr, _, auxr, prin1), NegLeftRule(upl, _, auxl, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        CutRule(upl, upr, auxl, auxr)
    // TODO: add quantifier cases here
    case _ => reduceRank(left, right, cutFormula1, cutFormula2)
  }

    // Rank reduction rules:
  private def reduceRank(left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula): LKProof =
    (left, right) match {
    case (Axiom(_), proof: LKProof) => proof
    case (proof: LKProof, Axiom(_)) => proof
    case (WeakeningRightRule(up, _, prin), proof: LKProof) if prin.formula == cutFormula1 =>
      var tmp: LKProof = up
      var alreadySeen = false
      for (i <- proof.root.antecedent)
        if (i.formula != cutFormula2 || alreadySeen) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
        else alreadySeen = true
      for (i <- proof.root.succedent) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
      tmp
    case (proof: LKProof, WeakeningLeftRule(up, _, prin)) if prin.formula == cutFormula2 =>
      var tmp: LKProof = up
      var alreadySeen = false
      for (i <- proof.root.antecedent) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
      for (i <- proof.root.succedent)
        if (i.formula != cutFormula1 || alreadySeen) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
        else alreadySeen = true
      tmp
    case (ContractionRightRule(up, _, aux1, aux2, prin), proof: LKProof) if prin.formula == cutFormula1 =>
      val proof1 = renameEigenVars(proof)
      var tmp: LKProof = CutRule(CutRule(up, proof, aux1.formula), proof1, aux2.formula)
      var alreadySeen = false
      for (i <- proof.root.antecedent)
        if (i.formula != cutFormula2 || alreadySeen) tmp = ContractionLeftRule(tmp, i.formula)
        else alreadySeen = true
      for (i <- proof.root.succedent) tmp = ContractionRightRule(tmp, i.formula)
      tmp
    case (proof: LKProof, ContractionLeftRule(up, _, aux1, aux2, prin)) if prin.formula == cutFormula1 =>
      val proof1 = renameEigenVars(proof)
      var tmp: LKProof = CutRule(proof1, CutRule(up, proof, aux1.formula), aux2.formula)
      var alreadySeen = false
      for (i <- proof.root.antecedent) tmp = ContractionLeftRule(tmp, i.formula)
      for (i <- proof.root.succedent)
        if (i.formula != cutFormula1 || alreadySeen) tmp = ContractionRightRule(tmp, i.formula)
        else alreadySeen = true
      tmp
    case (unary: UnaryLKProof, proof: LKProof) if cutFormula1 == cutFormula2 => reduceUnaryLeft(unary, proof, cutFormula1)
    case (binary: BinaryLKProof, proof: LKProof) if cutFormula1 == cutFormula2 => reduceBinaryLeft(binary, proof, cutFormula1)
    case _ =>
      throw new ReductiveCutElimException("Can't match the case: Cut(" + left.rule.toString + ", " + right.rule.toString + ")")
  }

  private def reduceUnaryLeft(unary: UnaryLKProof, proof: LKProof, cutFormula: HOLFormula): LKProof = unary match {
    case WeakeningLeftRule(up, _, prin) if prin.formula != cutFormula =>
      WeakeningLeftRule.createDefault(CutRule(up, proof, cutFormula), prin.formula)
    case WeakeningRightRule(up, _, prin) if prin.formula != cutFormula =>
      WeakeningRightRule.createDefault(CutRule(up, proof, cutFormula), prin.formula)
    case ContractionLeftRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ContractionLeftRule(CutRule(up, proof, cutFormula), aux1, aux2)
    case ContractionRightRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ContractionRightRule(CutRule(up, proof, cutFormula), aux1, aux2)
    case AndLeft1Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case And(aux.formula, f) => AndLeft1Rule(CutRule(up, proof, cutFormula), aux.formula, f)
    }
    case AndLeft2Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case And(f, aux.formula) => AndLeft2Rule(CutRule(up, proof, cutFormula), f, aux)
    }
    case OrRight1Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case Or(aux.formula, f) => OrRight1Rule(CutRule(up, proof, cutFormula), aux, f)
    }
    case OrRight2Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case Or(f, aux.formula) => OrRight2Rule(CutRule(up, proof, cutFormula), f, aux)
    }
    case ImpRightRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ImpRightRule(CutRule(up, proof, cutFormula), aux1, aux2)
    case NegLeftRule(up, _, aux, prin) if prin.formula != cutFormula =>
      NegLeftRule(CutRule(up, proof, cutFormula), aux)
    case NegRightRule(up, _, aux, prin) if prin.formula != cutFormula =>
      NegRightRule(CutRule(up, proof, cutFormula), aux)
    case _ => reduceUnaryLeftQ(unary, proof, cutFormula)
  }

  private def reduceUnaryLeftQ(unary: UnaryLKProof, proof: LKProof, cutFormula: HOLFormula): LKProof = unary match {
    case ForallLeftRule(up, _, aux, prin, subst) if prin.formula != cutFormula =>
      ForallLeftRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, subst)
    case ForallRightRule(up, _, aux, prin, eigenVar) if prin.formula != cutFormula =>
      ForallRightRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsLeftRule(up, _, aux, prin, eigenVar) if prin.formula != cutFormula =>
      ExistsLeftRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsRightRule(up, _, aux, prin, subst) if prin.formula != cutFormula =>
      ExistsRightRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, subst)
    case _ => proof match {
      case p: UnaryLKProof => reduceUnaryRight(unary, p, cutFormula)
      case p: BinaryLKProof => reduceBinaryRight(unary, p, cutFormula)
    }
  }

  private def reduceUnaryRight(proof: LKProof, unary: UnaryLKProof, cutFormula: HOLFormula): LKProof = unary match {
    case WeakeningLeftRule(up, _, prin) if prin.formula != cutFormula =>
      WeakeningLeftRule.createDefault(CutRule(proof, up, cutFormula), prin.formula)
    case WeakeningRightRule(up, _, prin) if prin.formula != cutFormula =>
      WeakeningRightRule.createDefault(CutRule(proof, up, cutFormula), prin.formula)
    case ContractionLeftRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ContractionLeftRule(CutRule(proof, up, cutFormula), aux1, aux2)
    case ContractionRightRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ContractionRightRule(CutRule(proof, up, cutFormula), aux1, aux2)
    case AndLeft1Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case And(aux.formula, f) => AndLeft1Rule(CutRule(proof, up, cutFormula), aux, f)
    }
    case AndLeft2Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case And(f, aux.formula) => AndLeft2Rule(CutRule(proof, up, cutFormula), f, aux)
    }
    case OrRight1Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case Or(aux.formula, f) => OrRight1Rule(CutRule(proof, up, cutFormula), aux, f)
    }
    case OrRight2Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case Or(f, aux.formula) => OrRight2Rule(CutRule(proof, up, cutFormula), f, aux)
    }
    case ImpRightRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ImpRightRule(CutRule(proof, up, cutFormula), aux1, aux2)
    case NegLeftRule(up, _, aux, prin) if prin.formula != cutFormula =>
      NegLeftRule(CutRule(proof, up, cutFormula), aux)
    case NegRightRule(up, _, aux, prin) if prin.formula != cutFormula =>
      NegRightRule(CutRule(proof, up, cutFormula), aux)
    case _ => reduceUnaryRightQ(proof, unary, cutFormula)
  }

  private def reduceUnaryRightQ(proof: LKProof, unary: UnaryLKProof, cutFormula: HOLFormula): LKProof = unary match {
    case ForallLeftRule(up, _, aux, prin, subst) if prin.formula != cutFormula =>
      ForallLeftRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, subst)
    case ForallRightRule(up, _, aux, prin, eigenVar) if prin.formula != cutFormula =>
      ForallRightRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsLeftRule(up, _, aux, prin, eigenVar) if prin.formula != cutFormula =>
      ExistsLeftRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsRightRule(up, _, aux, prin, subst) if prin.formula != cutFormula =>
      ExistsRightRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, subst)
    case _ =>
      throw new ReductiveCutElimException("Can't match the case: Cut(" + proof.rule.toString + ", " + unary.rule.toString + ")")
  }

  private def reduceBinaryLeft(binary: BinaryLKProof, proof: LKProof, cutFormula: HOLFormula): LKProof = binary match {
    case AndRightRule(up1, up2, _, aux1, aux2, prin) /* if prin.formula != cutFormula*/ =>
      if ((aux1.formula != cutFormula && up1.root.succedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.succedent.find(x => x.formula == cutFormula).size > 1))
        AndRightRule(CutRule(up1, proof, cutFormula), up2, aux1, aux2)
      else //if ((aux2.formula != cutFormula && up2.root.succedent.exists(x => x.formula == cutFormula)) ||
       // (aux2.formula == cutFormula && up2.root.succedent.find(x => x.formula == cutFormula).size > 1))
        AndRightRule(up1, CutRule(up2, proof, cutFormula), aux1, aux2)
     // else throw new ReductiveCutElimException("Can't find cut-formula!")
    case OrLeftRule(up1, up2, _, aux1, aux2, prin) /* if prin.formula != cutFormula*/ =>
      if ((aux1.formula != cutFormula && up1.root.succedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.succedent.find(x => x.formula == cutFormula).size > 1))
        OrLeftRule(CutRule(up1, proof, cutFormula), up2, aux1, aux2)
      else// if ((aux2.formula != cutFormula && up2.root.succedent.exists(x => x.formula == cutFormula)) ||
       // (aux2.formula == cutFormula && up2.root.succedent.find(x => x.formula == cutFormula).size > 1))
        OrLeftRule(up1, CutRule(up2, proof, cutFormula), aux1, aux2)
     // else throw new ReductiveCutElimException("Can't find cut-formula!")
    case ImpLeftRule(up1, up2, _, aux1, aux2, prin) /* if prin.formula != cutFormula */ =>
      if ((aux1.formula != cutFormula && up1.root.succedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.succedent.find(x => x.formula == cutFormula).size > 1))
        ImpLeftRule(CutRule(up1, proof, cutFormula), up2, aux1, aux2)
      else //if ((aux2.formula != cutFormula && up2.root.succedent.exists(x => x.formula == cutFormula)) ||
       // (aux2.formula == cutFormula && up2.root.succedent.find(x => x.formula == cutFormula).size > 1))
        ImpLeftRule(up1, CutRule(up2, proof, cutFormula), aux1, aux2)
     // else throw new ReductiveCutElimException("Can't find cut-formula!")
  //  case CutRule(up1, up2, _, a1, a2) => reduceCut(up1, up2, a1.formula, a2.formula)
    case _ => proof match {
      case p: UnaryLKProof => reduceUnaryRight(binary, p, cutFormula)
      case p: BinaryLKProof => reduceBinaryRight(binary, p, cutFormula)
    }
  }

  private def reduceBinaryRight(proof: LKProof, binary: BinaryLKProof, cutFormula: HOLFormula): LKProof = binary match {
    case AndRightRule(up1, up2, _, aux1, aux2, prin) /*if prin.formula != cutFormula */=>
      if ((aux1.formula != cutFormula && up1.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        AndRightRule(CutRule(proof, up1, cutFormula), up2, aux1, aux2)
      else //if ((aux2.formula != cutFormula && up2.root.antecedent.exists(x => x.formula == cutFormula)) ||
       // (aux2.formula == cutFormula && up2.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        AndRightRule(up1, CutRule(proof, up2, cutFormula), aux1, aux2)
     // else throw new ReductiveCutElimException("Can't find cut-formula!")
    case OrLeftRule(up1, up2, _, aux1, aux2, prin) /* if prin.formula != cutFormula */=>
      if ((aux1.formula != cutFormula && up1.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        OrLeftRule(CutRule(proof, up1, cutFormula), up2, aux1, aux2)
      else// if ((aux2.formula != cutFormula && up2.root.antecedent.exists(x => x.formula == cutFormula)) ||
       // (aux2.formula == cutFormula && up2.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        OrLeftRule(up1, CutRule(proof, up2, cutFormula), aux1, aux2)
     // else throw new ReductiveCutElimException("Can't find cut-formula!")
    case ImpLeftRule(up1, up2, _, aux1, aux2, prin)/* if prin.formula != cutFormula*/ =>
      if ((aux1.formula != cutFormula && up1.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        ImpLeftRule(CutRule(proof, up2, cutFormula), up2, aux1, aux2)
      else //if ((aux2.formula != cutFormula && up2.root.antecedent.exists(x => x.formula == cutFormula)) ||
       // (aux2.formula == cutFormula && up2.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        ImpLeftRule(up1, CutRule(proof, up2, cutFormula), aux1, aux2)
     // else throw new ReductiveCutElimException("Can't find cut-formula!")
  //  case CutRule(up1, up2, _, a1, a2) => reduceCut(up1, up2, a1.formula, a2.formula)
    case _ =>
      throw new ReductiveCutElimException("Can't match the case: Cut(" + proof.rule.toString + ", " + binary.rule.toString + ")")
  }
     // TODO: implement method below
  def renameEigenVars(proof: LKProof) = proof                   */
}