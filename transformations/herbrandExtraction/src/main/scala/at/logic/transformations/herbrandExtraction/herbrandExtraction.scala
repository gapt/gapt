/**
 * Herbrand sequent extraction
 *
 * ATTENTION: this herbrand sequent extraction relies heavily
 * on the fact that the positions of the formulas on the sequent
 * is maintained and can be discovered.
 */

package at.logic.transformations.herbrandExtraction

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.hol._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
import at.logic.calculi.lk.base.types._

class HerbrandExtractionException(msg: String) extends Exception(msg)

object ExtractHerbrandSequent {

  def apply(proof: LKProof) : FSequent = {
    val hs = buildHerbrand(proof)
    val exphs = expandArrays(hs)
    exphs
  }

  // Expand herbrand arrays of the type (A o <B, C>) to formulas A o B, A o C
  // (where 'o' is a connective)
  private def expandArrays(seq: Sequent) : FSequent = {
    val newant = seq.antecedent.foldLeft (Seq[HOLFormula]()) ((acc, f) => (expand (f.formula)) ++ acc)
    val newsucc = seq.succedent.foldLeft (Seq[HOLFormula]()) ((acc, f) => (expand (f.formula)) ++ acc)
    new FSequent(newant, newsucc)
  }

  private def expand(f: HOLFormula) : Seq[HOLFormula] = f match {
    case And(a, b) => 
      val left = expand(a) 
      val right = expand(b)
      for(fa <- left; fb <- right) yield { And(fa, fb) }
    case Or(a, b) =>
      val left = expand(a) 
      val right = expand(b)
      for(fa <- left; fb <- right) yield { Or(fa, fb) }
    case Imp(a, b) =>
      val left = expand(a) 
      val right = expand(b)
      for(fa <- left; fb <- right) yield { Imp(fa, fb) }
    case Neg(a) => expand(a).map(x => Neg(x))
    case HArray(a, b) => expand(a) ++ expand(b)
    case Atom(_, _) => f::Nil
    // TODO: ignoring quantified formulas that eventually ended up in the
    // Herbrand sequent. Is this the correct way to treat it??
    case AllVar(_, _) => Nil
    case ExVar(_, _) => Nil
    case _ => throw new HerbrandExtractionException("Illegal formula on Herbrand sequent: " + f.toString)
  }

  private def getOccSamePosition(s1: Seq[FormulaOccurrence], f: FormulaOccurrence, s2: Seq[FormulaOccurrence]) = {
    val i = s1.indexOf(f)
    s2(i)
  }

  private def getTheOtherForm(prin: HOLFormula, aux: HOLFormula) = prin match {
    case And(f1, f2) if (f2 == aux) => f1
    case And(f1, f2) if (f1 == aux) => f2
    case Or(f1, f2) if (f2 == aux) => f1
    case Or(f1, f2) if (f1 == aux) => f2
    case _ => throw new HerbrandExtractionException("Trying to get the other formula from something that is not a conjunction or disjunction.")
  }

  private def buildHerbrand(proof: LKProof) : Sequent = proof match {

    /* AXIOM */
    // The Herbrand sequent is the axiom itself
    case Axiom(s) => s

    /* WEAKENING RULES */
    // Put the weakened formula back in the sequent
    case WeakeningLeftRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      WeakeningLeftRule(hs, pf.formula)
    case WeakeningRightRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      WeakeningRightRule(hs, pf.formula)

    /* CONTRACTION RULES */
    // Find the contracted formulas (aux1, aux2) on the sequent returned from the recursive call
    // and make one occurrence of both.
    // OBS: if these formulas were quantified, the contracted formulas are not
    // equal and should be joined in a herbrand array
    case ContractionLeftRule(up, _, aux1, aux2, prin) =>
      val hs = buildHerbrand(up)
      // Get the indexes from the aux formulas.
      // Find the formulas with these same indexes in hs
      // Pass these occurrences to the apply method of ContractionLeftRule
      // (overloaded)
      // Find the corresponding formulas in hs
      val aux1hs = getOccSamePosition(up.root.antecedent, aux1, hs.antecedent)
      val aux2hs = getOccSamePosition(up.root.antecedent, aux2, hs.antecedent)
      // If these formulas are different, they are instantiations of a
      // quantified formula. So, join them in a herbrand array op.
      if(aux1hs.formula != aux2hs.formula){
        val ha = HArray(aux1hs.formula, aux2hs.formula)
        val haocc = aux1hs.factory.createFormulaOccurrence(ha, aux1hs.ancestors ++ aux2hs.ancestors)
        // Creating the sequent by hand (choosing this solution so that the code
        // from propositionalRules is not polluted with ifs).
        val ant1 = createContext(hs.antecedent.filterNot(x =>  x == aux1hs || x == aux2hs))
        val antecedent = ant1 :+ haocc
        val succedent = createContext(hs.succedent)
        Sequent(antecedent, succedent)
      }
      // Pass these occurrences to the apply method of ContractionLeftRule
      else ContractionLeftRule(hs, aux1hs, aux2hs)
    case ContractionRightRule(up, _, aux1, aux2, prin) =>
      val hs = buildHerbrand(up)
      // Find the corresponding formulas in hs
      val aux1hs = getOccSamePosition(up.root.succedent, aux1, hs.succedent)
      val aux2hs = getOccSamePosition(up.root.succedent, aux2, hs.succedent)
      // If these formulas are different, they are instantiations of a
      // quantified formula. So, join them in a herbrand array op.
      if(aux1hs.formula != aux2hs.formula){
        val ha = HArray(aux1hs.formula, aux2hs.formula)
        val haocc = aux1hs.factory.createFormulaOccurrence(ha, aux1hs.ancestors ++ aux2hs.ancestors)
        // Creating the sequent by hand (choosing this solution so that the code
        // from propositionalRules is not polluted with ifs).
        val antecedent = createContext(hs.antecedent)
        val suc1 = createContext(hs.succedent.filterNot(x =>  x == aux1hs || x == aux2hs))
        val succedent = suc1 :+ haocc
        Sequent(antecedent, succedent)
      }
      // Pass these occurrences to the apply method of ContractionRightRule
      else ContractionRightRule(hs, aux1hs, aux2hs)

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
      val other = getTheOtherForm(prin.formula, aux.formula)
      AndLeft1Rule(hs, auxhs, other)
    // newHS = {hs.ant \ {B}} U {A ^ B} |- hs.succ
    case AndLeft2Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.antecedent, aux, hs.antecedent)
      val other = getTheOtherForm(prin.formula, aux.formula)
      AndLeft2Rule(hs, other, auxhs)

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
      val other = getTheOtherForm(prin.formula, aux.formula)
      OrRight1Rule(hs, auxhs, other)
    // newHS = hs.ant |- {hs.succ \ {B}} U {A v B}
    case OrRight2Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
      val auxhs = getOccSamePosition(up.root.succedent, aux, hs.succedent)
      val other = getTheOtherForm(prin.formula, aux.formula)
      OrRight2Rule(hs, other, auxhs)

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
      buildHerbrand(up)
    case ExistsRightRule(up, _, aux, prin, term) =>
      buildHerbrand(up)

    // TODO: equalities

    /* STRONG QUANTIFIER RULES */
    // Should not occur
    case ExistsLeftRule(_, _, _, _, _) | ForallRightRule(_, _, _, _, _) =>
      throw new HerbrandExtractionException("ERROR: Found strong quantifier rule while extracting Herbrand sequent.")

    // Assuming that the formulas in a1 and a2 are the same
    case CutRule(up1, up2, _, a1, a2) => a1.formula.containsQuantifier match {
      case true => throw new HerbrandExtractionException("ERROR: Found cut with quantifier.")
      case _ =>
        val hs1 = buildHerbrand(up1)
        val hs2 = buildHerbrand(up2)
        val aux1hs = getOccSamePosition(up1.root.succedent, a1, hs1.succedent)
        val aux2hs = getOccSamePosition(up2.root.antecedent, a2, hs2.antecedent)
        CutRule(hs1, hs2, aux1hs, aux2hs)
    }
  }
}

