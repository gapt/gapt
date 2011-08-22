/**
 * Created by IntelliJ IDEA.
 * User: giselle
 * Date: 8/18/11
 * Time: 5:14 PM
 * To change this template use File | Settings | File Templates.
 */

package transformations.herbrand_extraction

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.fol._
import at.logic.calculi.occurrences._

class HerbrandExtractionException(msg: String) extends Exception(msg)

object herbrandExtraction{
  //private var hseq : Sequent = Sequent(Nil, Nil)

  def apply(proof: LKProof) : Sequent = {
    //hseq = Sequent(Nil, Nil) // Start from the empty sequent
    buildHerbrand(proof)
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
      val fopf = pf.formula.asInstanceOf[FOLFormula]
      Sequent(fopf::hs.antecedent, hs.succedent)
    case WeakeningRightRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      val fopf = pf.formula.asInstanceOf[FOLFormula]
      Sequent(hs.antecedent, fopf::hs.succedent)

    /* CONTRACTION RULES */
    // Find the contracted formulas (aux1, aux2?) on the sequent returned from the recursive call
    // and make one occurrence of both.
    // OBS: if these formulas were quantified, the contracted formulas will be on the head of a herbrand array
    // and the arrays should be merged.
    // TODO
    case ContractionLeftRule(up, _, aux1, aux2, prin) =>
      val hs = buildHerbrand(up)
    // TODO
    case ContractionRightRule(up, _, aux1, aux2, prin) =>
      val hs = buildHerbrand(up)

    /* RIGHT CONJUNCTION RULE */
    // Find the formulas A and B from (A ^ B) on the two sequents returned from the recursive calls
    // and build a new sequent with all the formulas from both but replacing A and B with (A ^ B)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = hs1.ant U hs2.ant |- {hs1.succ \ {A}} U {hs2.succ \ {B}} U {A ^ B}
    case AndRightRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)

    /* LEFT CONJUNCTION RULES */
    // Find the formula A (or B) from (A ^ B) on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A (or B) with (A ^ B)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = {hs.ant \ {A}} U {A ^ B} |- hs.succ
    case AndLeft1Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
    // TODO
    // newHS = {hs.ant \ {B}} U {A ^ B} |- hs.succ
    case AndLeft2Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)

    /* LEFT DISJUNCTION RULE */
    // Find the formulas A and B from (A v B) on the two sequents returned from the recursive calls
    // and build a new sequent with all the formulas from both but replacing A and B with (A v B)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = {hs1.ant \ {A}} U {hs2.ant \ {B}} U {A v B} |- hs1.succ U hs2.succ
    case OrLeftRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)

    /* RIGHT DISJUNCTION RULES */
    // Find the formula A (or B) from (A v B) on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A (or B) with (A v B)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = hs.ant |- {hs.succ \ {A}} U {A v B}
    case OrRight1Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)
    // TODO
    // newHS = hs.ant |- {hs.succ \ {B}} U {A v B}
    case OrRight2Rule(up, _, aux, prin) =>
      val hs = buildHerbrand(up)

    /* LEFT IMPLICATION RULE */
    // Find the formula A and B from (A -> B) on the sequents returned from the recursive calls
    // and build a new sequent with all the formulas from both but replacing A and B with (A -> B)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = hs1.ant U {hs2.ant \ {B}} U {A -> B}|- {hs1.succ \ {A}} U hs2.succ
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)

    /* RIGHT IMPLICATION RULE */
    // Find the formula A and B from (A -> B) on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A and B with (A -> B)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = hs.ant \ {A} |- {hs.succ \ {B}} U {A -> B}
    case ImpRightRule(up, _, aux1, aux2, _) =>
      val hs = buildHerbrand(up)

    /* NEGATION RULES */
    // Find the negated formula A on the sequent returned from the recursive call
    // and build a new sequent with all the formulas from it but replacing A with (not A)
    // OBS: The formula might be the head of a herbrand sequent.
    // TODO
    // newHS = hs.ant U {not A} |- hs.succ \ {A}
    case NegLeftRule(up, _, aux, _) =>
      val hs = buildHerbrand(up)
    // TODO
    // newHS = hs.ant \ {A} |- hs.succ U {not A}
    case NegRightRule(up, _, aux, _) =>
      val hs = buildHerbrand(up)

    /* WEAK QUANTIFIER RULES */
    // This is when the Herbrand array is created. Take the instantiated formula from the sequent
    // returned from the recursive call, and create a Herbrand array where the head is prin and the
    // body is the instantiated formula.
    // OBS: This instantiated formula might be in the head of a herbrand array. In this case, it must
    // be that there were two quantifiers. So:
    /*
              |- P(a, b)           (1)
          ------------------
           |- EX y. P(a, y)        (2)
      --------------------------
        |- EX x. EX y. P(x, y)     (3)


     In (1), the herbrand sequent H1 contains only P(a,b) and no arrays.
     To build the herbrand sequent H2 of (2), we must find the occurrence of P(a,b) in H1 and replace it
     with [EX y. P(a,y)]<P(a,b)>.
     To build the herbrand sequent H3 of (3), we must find the occurrences of EX y. P(a,y). But in this case,
     this occurrence is in the head of a herbrand array, so all we need to do is update this head and we'll
     have [EX x. EX y. P(x,y)]<P(a,b)>.
    */
    // TODO
    case ForallLeftRule(up, _, aux, prin, term) =>
      val hs = buildHerbrand(up)
      val ha = HArray(prin.asInstanceOf[FOLFormula], (aux.asInstanceOf[FOLFormula]::Nil))
      // Remove aux from the herbrand sequent, it is added in the herbrand array above.
      val ant = hs.antecedent.filterNot(x => x == aux)
      Sequent(ha::hs.antecedent, hs.succedent)
    // TODO
    case ExistsRightRule(up, _, aux, prin, term) =>
      val hs = buildHerbrand(up)
      val ha = HArray(prin.asInstanceOf[FOLFormula], (aux.asInstanceOf[FOLFormula]::Nil))
      // Remove aux from the herbrand sequent, it is added in the herbrand array above.
      val ant = hs.succedent.filterNot(x => x == aux)
      Sequent(hs.antecedent, ha::hs.succedent)

    /* DEFINITION RULES */
    // TODO: find out what they are.
    case DefinitionLeftRule(up, _, aux, prin) =>
    // TODO
    case DefinitionRightRule(up, _, aux, prin) =>

    /* STRONG QUANTIFIER RULES */
    // Should not occur
    case ExistsLeftRule(_, _, _, _, _) | ForallRightRule(_, _, _, _, _) =>
      throw new HerbrandExtractionException("ERROR: Found strong quantifier rule while extracting Herbrand sequent.")

    case CutRule(_, _, _, a1, a2) => 
    // TODO: throw exception only if the formula has quantifiers.
  }

  // This method creates or updates a Herbrand array when weak quantifier rules are applied (no it doesn't...)
  // Decide about formula and formula occurrences before going on.
  def weakQuant(conc : FormulaOccurrence, prem : FormulaOccurrence, lst : List[FOLFormula]) = {
    val fo = findOccurrence(prem, lst)
    val newocc = fo match {
      case HArray(prem, l) => HArray(conc, l)
      case prem => HArray(conc, prem::Nil)
    }
    newocc :: lst.filter(x => x != fo)
  }

  // Finds the occurrence of a formula on a list of formulas if it's explicit or the head of a Herbrand array.
  def findOccurrence(f : FormulaOccurrence, lst : List[FOLFormula]) = lst match {
    case Nil => throw new HerbrandExtractionException("ERROR: Did not find the formula in the sequent.")
    case h :: tl => h match {
      // TODO: can I compare FormulaOccurrence with ==?
      case HArray(orig, l) => if (orig == f) h else findOccurrence(f, tl)
      case x => if (x == f) h else findOccurrence(f, tl)
    }

  }


}
