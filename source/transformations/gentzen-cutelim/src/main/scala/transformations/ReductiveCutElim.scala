/*
 * ReductiveCutElim.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations


import java.lang.Exception
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.base._
import at.logic.language.hol._
import at.logic.calculi.occurrences._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.algorithms.lk.{regularize, applySubstitution}

class ReductiveCutElimException(msg: String) extends Exception(msg)

object ReductiveCutElim {
  private var proofList: List[LKProof] = Nil

  def proofs = proofList

  def apply(proof: LKProof): LKProof = {
    proofList = Nil
    val pr = cutElim(regularize(proof)._1)
    proofList = proofList:::(pr::Nil)
    pr
  }

 /* private def cutElim(proof: LKProof): LKProof = {
    proofList = proofList:::(proof::Nil)
    cutElim1(proof)
  }*/

  private def cutElim(proof: LKProof): LKProof = proof match {
    case Axiom(_) => proof
    case WeakeningLeftRule(up, _, pf) => WeakeningLeftRule.createDefault(cutElim(up), pf.formula)
    case WeakeningRightRule(up, _, pf) => WeakeningRightRule.createDefault(cutElim(up), pf.formula)
    case ContractionLeftRule(up, _, aux, _, _) => ContractionLeftRule(cutElim(up), aux.formula)
    case ContractionRightRule(up, _, aux, _, _) => ContractionRightRule(cutElim(up), aux.formula)
    case AndRightRule(up1, up2, _, aux1, aux2, _) => AndRightRule(cutElim(up1), cutElim(up2), aux1.formula, aux2.formula)
    case AndLeft1Rule(up, _, aux, prin) => prin.formula match {
      case And(aux.formula, f) => AndLeft1Rule(cutElim(up), aux.formula, f)
    }
    case AndLeft2Rule(up, _, aux, prin) => prin.formula match {
      case And(f, aux.formula) => AndLeft2Rule(cutElim(up), f, aux.formula)
    }
    case OrLeftRule(up1, up2, _, aux1, aux2, _) => OrLeftRule(cutElim(up1), cutElim(up2), aux1.formula, aux2.formula)
    case OrRight1Rule(up, _, aux, prin) => prin.formula match {
      case Or(aux.formula, f) => OrRight1Rule(cutElim(up), aux.formula, f)
    }
    case OrRight2Rule(up, _, aux, prin) => prin.formula match {
      case Or(f, aux.formula) => OrRight2Rule(cutElim(up), f, aux.formula)
    }
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) => ImpLeftRule(cutElim(up1), cutElim(up2), aux1.formula, aux2.formula)
    case ImpRightRule(up, _, aux1, aux2, _) => ImpRightRule(cutElim(up), aux1.formula, aux2.formula)
    case NegLeftRule(up, _, aux, _) => NegLeftRule(cutElim(up), aux.formula)
    case NegRightRule(up, _, aux, _) => NegRightRule(cutElim(up), aux.formula)
    case ForallLeftRule(up, _, aux, prin, term) => ForallLeftRule(cutElim(up), aux.formula, prin.formula, term)
    case ForallRightRule(up, _, aux, prin, eigenVar) => ForallRightRule(cutElim(up), aux.formula, prin.formula, eigenVar)
    case ExistsLeftRule(up, _, aux, prin, eigenVar) => ExistsLeftRule(cutElim(up), aux.formula, prin.formula, eigenVar)
    case ExistsRightRule(up, _, aux, prin, term) => ExistsRightRule(cutElim(up), aux.formula, prin.formula, term)
    case DefinitionLeftRule(up, _, aux, prin) => DefinitionLeftRule(cutElim(up), aux.formula, prin.formula)
    case DefinitionRightRule(up, _, aux, prin) => DefinitionRightRule(cutElim(up), aux.formula, prin.formula)
    case CutRule(up1, up2, _, a1, a2) => cutElim(reduceCut(up1, up2, a1.formula, a2.formula))
  }

  private def reduceCut(left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula): LKProof =
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
    case _ => reduceGradeQ(left, right, cutFormula1, cutFormula2)
  }

  private def reduceGradeQ(left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula): LKProof =
    (left, right) match {
    case (ForallRightRule(up1, _, aux1, prin1, eigenVar), ForallLeftRule(up2, _, aux2, prin2, term))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        val up = applySubstitution(up1, Substitution(eigenVar, term))._1
        CutRule(up, up2, aux2.formula)
    case (ExistsRightRule(up1, _, aux1, prin1, term), ExistsLeftRule(up2, _, aux2, prin2, eigenVar))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        val up = applySubstitution(up2, Substitution(eigenVar, term))._1
        CutRule(up1, up, aux1.formula)
    case (DefinitionRightRule(up1, _, aux1, prin1), DefinitionLeftRule(up2, _, aux2, prin2))
      if (prin1.formula == cutFormula1 && prin2.formula == cutFormula2) =>
        CutRule(up1, up2, aux1, aux2)
    case _ => reduceRank(left, right, cutFormula1, cutFormula2)
  }

    // Rank reduction rules:
  private def reduceRank(left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula): LKProof =
    (left, right) match {
    case (Axiom(_), proof: LKProof) => proof
    case (proof: LKProof, Axiom(_)) => proof
 //   case (WeakeningRightRule(up, _, prin), proof: LKProof) =>  //TODO: can't match this, why???
    case (proof: LKProof, WeakeningLeftRule(up, _, prin)) =>
      if (prin.formula == cutFormula2) {
        var tmp: LKProof = up
        var alreadySeen = false
        for (i <- proof.root.antecedent) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
        for (i <- proof.root.succedent)
          if (i.formula != cutFormula1 || alreadySeen) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
          else alreadySeen = true
        tmp
      }
      else WeakeningLeftRule.createDefault(CutRule(proof, up, cutFormula2), prin.formula)
 //   case (ContractionRightRule(up, _, aux1, aux2, prin), proof: LKProof) => //TODO: can't match this, why???
    case (proof: LKProof, ContractionLeftRule(up, _, aux1, aux2, prin)) =>
      if (prin.formula == cutFormula2) {
        val proof1 = regularize(proof)._1
        var tmp: LKProof = CutRule(proof1, CutRule(proof, up, aux1.formula), aux2.formula)
        var alreadySeen = false
        for (i <- proof.root.antecedent) tmp = ContractionLeftRule(tmp, i.formula)
        for (i <- proof.root.succedent)
          if (i.formula != cutFormula1 || alreadySeen) tmp = ContractionRightRule(tmp, i.formula)
          else alreadySeen = true
        regularize(tmp)._1
      }
      else ContractionLeftRule(CutRule(proof, up, cutFormula2), aux1.formula)
    case (unary: UnaryLKProof, proof: LKProof) =>
      if (unary.rule == WeakeningRightRuleType) {
        val unap = WeakeningRightRule.unapply(unary)
        if (unap == None)
          throw new ReductiveCutElimException("Can't match case: \n cut left premice is: " + unary.toString.replaceAll(",", "\n") +
            "\n\n cut right premice is: " + proof.toString.replaceAll(",", "\n"))
        val up = unap.get._1
        val prin =  unap.get._3
        if (prin.formula == cutFormula1) {
          var tmp: LKProof = up
          var alreadySeen = false
          for (i <- proof.root.antecedent)
            if (i.formula != cutFormula2 || alreadySeen) tmp = WeakeningLeftRule.createDefault(tmp, i.formula)
            else alreadySeen = true
          for (i <- proof.root.succedent) tmp = WeakeningRightRule.createDefault(tmp, i.formula)
          tmp
        }
        else WeakeningRightRule.createDefault(CutRule(up, proof, cutFormula1), prin.formula)
      } else if (unary.rule == ContractionRightRuleType) {
        val unap = ContractionRightRule.unapply(unary)
        if (unap == None)
          throw new ReductiveCutElimException("Can't match case: \n cut left premice is: " + unary.toString.replaceAll(",", "\n") +
            "\n\n cut right premice is: " + proof.toString.replaceAll(",", "\n"))
        val up = unap.get._1
        val aux1 = unap.get._3
        val aux2 = unap.get._4
        val prin = unap.get._5
        if (prin.formula == cutFormula1) {
          val proof1 = regularize(proof)._1
          var tmp: LKProof = CutRule(CutRule(up, proof, aux1.formula), proof1, aux2.formula)
          var alreadySeen = false
          for (i <- proof.root.antecedent)
            if (i.formula != cutFormula2 || alreadySeen) tmp = ContractionLeftRule(tmp, i.formula)
            else alreadySeen = true
          for (i <- proof.root.succedent) tmp = ContractionRightRule(tmp, i.formula)
          regularize(tmp)._1
        }
        else ContractionRightRule(CutRule(up, proof, cutFormula1), aux1.formula)
      } else reduceUnaryLeft(unary, proof, cutFormula1)
    case (binary: BinaryLKProof, proof: LKProof) => reduceBinaryLeft(binary, proof, cutFormula1)
    case _ =>
      throw new ReductiveCutElimException("Can't match the case: Cut(" + left.rule.toString + ", " + right.rule.toString + ")")
  }

  private def reduceUnaryLeft(unary: UnaryLKProof, proof: LKProof, cutFormula: HOLFormula): LKProof = unary match {
    case WeakeningLeftRule(up, _, prin) =>
      WeakeningLeftRule.createDefault(CutRule(up, proof, cutFormula), prin.formula)
    case ContractionLeftRule(up, _, aux, _, prin) =>
      ContractionLeftRule(CutRule(up, proof, cutFormula), aux.formula)
    case DefinitionLeftRule(up, _, aux, prin) =>
      DefinitionLeftRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula)
    case DefinitionRightRule(up, _, aux, prin) if (prin.formula != cutFormula) =>
      DefinitionRightRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula)
    case AndLeft1Rule(up, _, aux, prin) => prin.formula match {
      case And(aux.formula, f) => AndLeft1Rule(CutRule(up, proof, cutFormula), aux.formula, f)
    }
    case AndLeft2Rule(up, _, aux, prin) => prin.formula match {
      case And(f, aux.formula) => AndLeft2Rule(CutRule(up, proof, cutFormula), f, aux.formula)
    }
    case OrRight1Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case Or(aux.formula, f) => OrRight1Rule(CutRule(up, proof, cutFormula), aux.formula, f)
    }
    case OrRight2Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case Or(f, aux.formula) => OrRight2Rule(CutRule(up, proof, cutFormula), f, aux.formula)
    }
    case ImpRightRule(up, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      ImpRightRule(CutRule(up, proof, cutFormula), aux1.formula, aux2.formula)
    case NegLeftRule(up, _, aux, prin) =>
      NegLeftRule(CutRule(up, proof, cutFormula), aux.formula)
    case NegRightRule(up, _, aux, prin) if prin.formula != cutFormula =>
      NegRightRule(CutRule(up, proof, cutFormula), aux.formula)
    case ForallLeftRule(up, _, aux, prin, term) =>
      ForallLeftRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, term)
    case ForallRightRule(up, _, aux, prin, eigenVar) if prin.formula != cutFormula =>
      ForallRightRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsLeftRule(up, _, aux, prin, eigenVar) =>
      ExistsLeftRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsRightRule(up, _, aux, prin, term) if prin.formula != cutFormula =>
      ExistsRightRule(CutRule(up, proof, cutFormula), aux.formula, prin.formula, term)
    case _ => proof match {
      case p: UnaryLKProof => reduceUnaryRight(unary, p, cutFormula)
      case p: BinaryLKProof => reduceBinaryRight(unary, p, cutFormula)
    }
  }

  private def reduceUnaryRight(proof: LKProof, unary: UnaryLKProof, cutFormula: HOLFormula): LKProof = unary match {
    case WeakeningRightRule(up, _, prin) =>
      WeakeningRightRule.createDefault(CutRule(proof, up, cutFormula), prin.formula)
    case ContractionRightRule(up, _, aux, _, prin) =>
      ContractionRightRule(CutRule(proof, up, cutFormula), aux.formula)
    case DefinitionLeftRule(up, _, aux, prin) if (prin.formula != cutFormula) =>
      DefinitionLeftRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula)
    case DefinitionRightRule(up, _, aux, prin) =>
      DefinitionRightRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula)
    case AndLeft1Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case And(aux.formula, f) => AndLeft1Rule(CutRule(proof, up, cutFormula), aux.formula, f)
    }
    case AndLeft2Rule(up, _, aux, prin) if prin.formula != cutFormula => prin.formula match {
      case And(f, aux.formula) => AndLeft2Rule(CutRule(proof, up, cutFormula), f, aux.formula)
    }
    case OrRight1Rule(up, _, aux, prin) => prin.formula match {
      case Or(aux.formula, f) => OrRight1Rule(CutRule(proof, up, cutFormula), aux.formula, f)
    }
    case OrRight2Rule(up, _, aux, prin) => prin.formula match {
      case Or(f, aux.formula) => OrRight2Rule(CutRule(proof, up, cutFormula), f, aux.formula)
    }
    case ImpRightRule(up, _, aux1, aux2, prin) =>
      ImpRightRule(CutRule(proof, up, cutFormula), aux1.formula, aux2.formula)
    case NegLeftRule(up, _, aux, prin) if prin.formula != cutFormula =>
      NegLeftRule(CutRule(proof, up, cutFormula), aux.formula)
    case NegRightRule(up, _, aux, prin) =>
      NegRightRule(CutRule(proof, up, cutFormula), aux.formula)
    case ForallLeftRule(up, _, aux, prin, term) if prin.formula != cutFormula =>
      ForallLeftRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, term)
    case ForallRightRule(up, _, aux, prin, eigenVar) =>
      ForallRightRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsLeftRule(up, _, aux, prin, eigenVar) if prin.formula != cutFormula =>
      ExistsLeftRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, eigenVar)
    case ExistsRightRule(up, _, aux, prin, term) =>
      ExistsRightRule(CutRule(proof, up, cutFormula), aux.formula, prin.formula, term)
    case _ =>
      throw new ReductiveCutElimException("Can't match the case: Cut(" + proof.rule.toString + ", " + unary.rule.toString + ")")
  }

  private def reduceBinaryLeft(binary: BinaryLKProof, proof: LKProof, cutFormula: HOLFormula): LKProof = binary match {
    case AndRightRule(up1, up2, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      if ((aux1.formula != cutFormula && up1.root.succedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.succedent.find(x => x.formula == cutFormula).size > 1))
        AndRightRule(CutRule(up1, proof, cutFormula), up2, aux1.formula, aux2.formula)
      else if ((aux2.formula != cutFormula && up2.root.succedent.exists(x => x.formula == cutFormula)) ||
        (aux2.formula == cutFormula && up2.root.succedent.find(x => x.formula == cutFormula).size > 1))
        AndRightRule(up1, CutRule(up2, proof, cutFormula), aux1.formula, aux2.formula)
      else throw new ReductiveCutElimException("Can't find cut-formula!")
    case OrLeftRule(up1, up2, _, aux1, aux2, prin) =>
      if (up1.root.succedent.exists(x => x.formula == cutFormula))
        OrLeftRule(CutRule(up1, proof, cutFormula), up2, aux1.formula, aux2.formula)
      else if (up2.root.succedent.exists(x => x.formula == cutFormula))
        OrLeftRule(up1, CutRule(up2, proof, cutFormula), aux1.formula, aux2.formula)
      else throw new ReductiveCutElimException("Can't find cut-formula!")
    case ImpLeftRule(up1, up2, _, aux1, aux2, prin) =>
      if (up1.root.succedent.exists(x => x.formula == cutFormula))
        ImpLeftRule(CutRule(up1, proof, cutFormula), up2, aux1.formula, aux2.formula)
      else if (up2.root.succedent.exists(x => x.formula == cutFormula))
        ImpLeftRule(up1, CutRule(up2, proof, cutFormula), aux1.formula, aux2.formula)
      else throw new ReductiveCutElimException("Can't find cut-formula!")
    case CutRule(up1, up2, _, a1, a2) => CutRule(reduceCut(up1, up2, a1.formula, a2.formula), proof, cutFormula)
    case _ => proof match {
      case p: UnaryLKProof => reduceUnaryRight(binary, p, cutFormula)
      case p: BinaryLKProof => reduceBinaryRight(binary, p, cutFormula)
    }
  }

  private def reduceBinaryRight(proof: LKProof, binary: BinaryLKProof, cutFormula: HOLFormula): LKProof = binary match {
    case AndRightRule(up1, up2, _, aux1, aux2, prin) =>
      if (up1.root.antecedent.exists(x => x.formula == cutFormula))
        AndRightRule(CutRule(proof, up1, cutFormula), up2, aux1.formula, aux2.formula)
      else if (up2.root.antecedent.exists(x => x.formula == cutFormula))
        AndRightRule(up1, CutRule(proof, up2, cutFormula), aux1.formula, aux2.formula)
      else throw new ReductiveCutElimException("Can't find cut-formula!")
    case OrLeftRule(up1, up2, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      if ((aux1.formula != cutFormula && up1.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        OrLeftRule(CutRule(proof, up1, cutFormula), up2, aux1.formula, aux2.formula)
      else if ((aux2.formula != cutFormula && up2.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux2.formula == cutFormula && up2.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        OrLeftRule(up1, CutRule(proof, up2, cutFormula), aux1.formula, aux2.formula)
      else throw new ReductiveCutElimException("Can't find cut-formula!")
    case ImpLeftRule(up1, up2, _, aux1, aux2, prin) if prin.formula != cutFormula =>
      if ((aux1.formula != cutFormula && up1.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux1.formula == cutFormula && up1.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        ImpLeftRule(CutRule(proof, up2, cutFormula), up2, aux1.formula, aux2.formula)
      else if ((aux2.formula != cutFormula && up2.root.antecedent.exists(x => x.formula == cutFormula)) ||
        (aux2.formula == cutFormula && up2.root.antecedent.find(x => x.formula == cutFormula).size > 1))
        ImpLeftRule(up1, CutRule(proof, up2, cutFormula), aux1.formula, aux2.formula)
      else throw new ReductiveCutElimException("Can't find cut-formula!")
    case CutRule(up1, up2, _, a1, a2) => CutRule(proof, reduceCut(up1, up2, a1.formula, a2.formula), cutFormula)
    case _ =>
      throw new ReductiveCutElimException("Can't match the case: Cut(" + proof.rule.toString + ", " + binary.rule.toString + ")")
  }
}