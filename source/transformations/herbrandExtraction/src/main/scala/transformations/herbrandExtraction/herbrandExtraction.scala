/**
 * Herbrand sequent extraction
 *
 * ATTENTION: this herbrand sequent extraction relies heavily
 * on the fact that the positions of the formulas on the sequent
 * is maintained and can be discovered.
 */

//package transformations.herbrand_extraction

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.immutable._

class HerbrandExtractionException(msg: String) extends Exception(msg)

object herbrandExtraction {
  
  // List that stores all the terms used in substitutions.
  var terms = Nil

  def apply(proof: LKProof) : Sequent = {
    buildHerbrand(proof)
  }

  private def getOccSamePosition(s1: Seq[FormulaOccurrence], f: FormulaOccurrence, s2: Seq[FormulaOccurrence]) = {
    val i = s1.indexOf(f)
    s2(i)
  }

  private def getTheOtherForm(prin: FOLFormula, aux: FOLFormula) = prin match {
    case And(f1, f2) if (f2 == aux) => f1
    case And(f1, f2) if (f1 == aux) => f2
    case Or(f1, f2) if (f2 == aux) => f1
    case Or(f1, f2) if (f1 == aux) => f2
    case _ => throw new HerbrandExtractionException("Trying to get the other formula from something that is not a conjunction or disjunction.")
  }

  private def buildHerbrand(proof: LKProof) : Sequent = proof match {

    /* AXIOM */
    // The Herbrand sequent is the axiom itself
    case Axiom(s) =>
      s.getSequent

    /* WEAKENING RULES */
    // Put the weakened formula back in the sequent
    case WeakeningLeftRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      WeakeningLeftRule(hs, pf)
    case WeakeningRightRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      WeakeningRightRule(hs, pf)

    /* CONTRACTION RULES */
    // Find the contracted formulas (aux1, aux2) on the sequent returned from the recursive call
    // and make one occurrence of both.
    // OBS: if these formulas were quantified, the contracted formulas are not
    // equal and should be joined in a herbrand array
    case ContractionLeftRule(up, _, aux1, aux2, prin) =>
      val hs = buildHerbrand(up)
      // Find the corresponding formulas in hs
      val aux1hs = getOccSamePosition(up.root.antecedent, aux1, hs.antecedent)
      val aux2hs = getOccSamePosition(up.root.antecedent, aux2, hs.antecedent)
      // If these formulas are different, they are instantiations of a
      // quantified formula. So, join them in a herbrand array op.
      if(aux1hs.formula != aux2hs.formula){
        val ha = HArray(aux1hs, aux2hs)
        aux1hs.formula = ha
        aux2hs.formula = ha
      }
      // Pass these occurrences to the apply method of ContractionLeftRule
      ContractionLeftRule(hs, aux1hs, aux2hs)
    case ContractionRightRule(up, _, aux1, aux2, prin) =>
      val hs = buildHerbrand(up)
      // Find the corresponding formulas in hs
      val aux1hs = getOccSamePosition(up.root.succedent, aux1, hs.succedent)
      val aux2hs = getOccSamePosition(up.root.succedent, aux2, hs.succedent)
      // If these formulas are different, they are instantiations of a
      // quantified formula. So, join them in a herbrand array op.
      if(aux1hs.formula != aux2hs.formula){
        val ha = HArray(aux1hs, aux2hs)
        aux1hs.formula = ha
        aux2hs.formula = ha
      }
      // Pass these occurrences to the apply method of ContractionLeftRule
      ContractionRightRule(hs, aux1hs, aux2hs)

    /* RIGHT CONJUNCTION RULE */
    // Find the formulas A and B from (A ^ B) on the two sequents returned from the recursive calls
    // and build a new sequent with all the formulas from both but replacing A and B with (A ^ B)
    // newHS = hs1.ant U hs2.ant |- {hs1.succ \ {A}} U {hs2.succ \ {B}} U {A ^ B}
    case AndRightRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)
      val aux1hs = getOccSamePosition(up1.root.succedent, aux1, hs1.succedent)
      val aux2hs = getOccSamePosition(up2.root.succedent, aux2, hs2.succedent)
      AndRightRule(hs1, hs2, aux1hs, aux2hs)

    /* LEFT CONJUNCTION RULES */
    // Find the formula A (or B) from (A ^ B) on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A (or B) with (A ^ B)
    // newHS = {hs.ant \ {A}} U {A ^ B} |- hs.succ
    case AndLeft1Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.antecedent, aux, hs.antecedent)
      val other = getTheOtherForm(prin, aux.formula)
      AndLeft1Rule(hs, auxhs, other)
    // newHS = {hs.ant \ {B}} U {A ^ B} |- hs.succ
    case AndLeft2Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.antecedent, aux, hs.antecedent)
      val other = getTheOtherForm(prin, aux.formula)
      AndLeft2Rule(hs, auxhs, other)

    /* LEFT DISJUNCTION RULE */
    // Find the formulas A and B from (A v B) on the two sequents returned from the recursive calls
    // and build a new sequent with all the formulas from both but replacing A and B with (A v B)
    // newHS = {hs1.ant \ {A}} U {hs2.ant \ {B}} U {A v B} |- hs1.succ U hs2.succ
    case OrLeftRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)
      val aux1hs = getOccSamePosition(up1.root.antecedent, aux1, hs1.antecedent)
      val aux2hs = getOccSamePosition(up2.root.antecedent, aux2, hs2.antecedent)
      OrLeftRule(hs1, hs2, aux1hs, aux2hs)

    /* RIGHT DISJUNCTION RULES */
    // Find the formula A (or B) from (A v B) on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A (or B) with (A v B)
    // newHS = hs.ant |- {hs.succ \ {A}} U {A v B}
    case OrRight1Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.succedent, aux, hs.succedent)
      val other = getTheOtherForm(prin, aux.formula)
      OrRight1Rule(hs, auxhs, other)
    // newHS = hs.ant |- {hs.succ \ {B}} U {A v B}
    case OrRight2Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.succedent, aux, hs.succedent)
      val other = getTheOtherForm(prin, aux.formula)
      OrRight2Rule(hs, auxhs, other)

    /* LEFT IMPLICATION RULE */
    // Find the formula A and B from (A -> B) on the sequents returned from the recursive calls
    // and build a new sequent with all the formulas from both but replacing A and B with (A -> B)
    // newHS = hs1.ant U {hs2.ant \ {B}} U {A -> B}|- {hs1.succ \ {A}} U hs2.succ
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)
      val aux1hs = getOccSamePosition(up1.root.succedent, aux1, hs1.succedent)
      val aux2hs = getOccSamePosition(up2.root.antecedent, aux2, hs2.antecedent)
      ImpLeftRule(hs1, hs2, aux1hs, aux2hs)

    /* RIGHT IMPLICATION RULE */
    // Find the formula A and B from (A -> B) on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A and B with (A -> B)
    // newHS = hs.ant \ {A} |- {hs.succ \ {B}} U {A -> B}
    case ImpRightRule(up, _, aux1, aux2, _) =>
      val hs = buildHerbrand(up)
      val aux1hs = getOccSamePosition(up.root.antecedent, aux1, hs.antecedent)
      val aux2hs = getOccSamePosition(up.root.succedent, aux2, hs.succedent)
      ImpRightRule(hs, aux1hs, aux2hs)

    /* NEGATION RULES */
    // Find the negated formula A on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A with (not A)
    // newHS = hs.ant U {not A} |- hs.succ \ {A}
    case NegLeftRule(up, _, aux, _) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.succedent, aux, hs.succedent)
      NegLeftRule(hs, auxhs)
    // newHS = hs.ant \ {A} |- hs.succ U {not A}
    case NegRightRule(up, _, aux, _) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.antecedent, aux, hs.antecedent)
      NegRightRule(hs, auxhs)

    /* WEAK QUANTIFIER RULES */
    case ForallLeftRule(up, _, aux, prin, term) =>
      // Save the term used for substitution
      terms = term :: terms
      // Return the same Herbrand sequent. We are not applying quantifier rules, 
      // we want the instantiated terms.
      buildHerbrand(up)
    case ExistsRightRule(up, _, aux, prin, term) =>
      // Save the term used for substitution
      terms = term :: terms
      // Return the same Herbrand sequent. We are not applying quantifier rules, 
      // we want the instantiated terms.
      buildHerbrand(up)

    /* DEFINITION RULES */
    // TODO: find out what they are.
    // Since Bruno is implementing an algorithm to eliminate definition rules, and that issue
    // is blocking the extraction of Herbrand sequents, I have a strong feeling that I will
    // not need to deal with this case.
    //case DefinitionLeftRule(up, _, aux, prin) =>
    // TODO
    //case DefinitionRightRule(up, _, aux, prin) =>

    /* STRONG QUANTIFIER RULES */
    // Should not occur
    case ExistsLeftRule(_, _, _, _, _) | ForallRightRule(_, _, _, _, _) =>
      throw new HerbrandExtractionException("ERROR: Found strong quantifier rule while extracting Herbrand sequent.")

    // Assuming that the formulas in a1 and a2 are the same
    case CutRule(up1, up2, _, a1, a2) => a1.formula match {
      case ExQ(_) | AllQ(_) => throw new HerbrandExtractionException("ERROR: Found cut with quantifier.")
      case _ =>
        val hs1 = buildHerbrand(up1)
        val hs2 = buildHerbrand(up2)
        val aux1hs = getOccSamePosition(up1.root.succedent, a1, hs1.succedent)
        val aux2hs = getOccSamePosition(up2.root.antecedent, a2, hs2.antecedent)
        CutRule(hs1, hs2, aux1hs, aux2hs)
    }
  }
}
