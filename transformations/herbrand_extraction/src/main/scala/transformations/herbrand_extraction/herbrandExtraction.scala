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

class HerbrandExtractionException(msg: String) extends Exception(msg)

object herbrandExtraction{
  //private var hseq : Sequent = Sequent(Nil, Nil)

  def apply(proof: LKProof) : Sequent = {
    //hseq = Sequent(Nil, Nil) // Start from the empty sequent
    buildHerbrand(proof)
  }

  private def buildHerbrand(proof: LKProof) : Sequent = proof match{

    case Axiom(s) => s.getSequent

    case WeakeningLeftRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      val fopf = pf.formula.asInstanceOf[FOLFormula]
      Sequent(fopf::hs.antecedent, hs.succedent)

    case WeakeningRightRule(up, _, pf) =>
      val hs = buildHerbrand(up)
      val fopf = pf.formula.asInstanceOf[FOLFormula]
      Sequent(hs.antecedent, fopf::hs.succedent)

    case ContractionLeftRule(up, _, aux, _, _) =>

    case ContractionRightRule(up, _, aux, _, _) =>

    case AndRightRule(up1, up2, _, aux1, aux2, _) =>
      val hs1 = buildHerbrand(up1)
      val hs2 = buildHerbrand(up2)
      hs1 // for compiling reasons.
      // TODO: combine these two herbrand sequents according to the rules.

    case AndLeft1Rule(up, _, aux, prin) =>

    case AndLeft2Rule(up, _, aux, prin) =>

    case OrLeftRule(up1, up2, _, aux1, aux2, _) =>

    case OrRight1Rule(up, _, aux, prin) =>

    case OrRight2Rule(up, _, aux, prin) =>

    case ImpLeftRule(up1, up2, _, aux1, aux2, _) =>

    case ImpRightRule(up, _, aux1, aux2, _) =>

    case NegLeftRule(up, _, aux, _) =>

    case NegRightRule(up, _, aux, _) =>

    case ForallLeftRule(up, _, aux, prin, term) =>

    case ExistsRightRule(up, _, aux, prin, term) =>

    case DefinitionLeftRule(up, _, aux, prin) =>

    case DefinitionRightRule(up, _, aux, prin) =>

    case ExistsLeftRule(_, _, _, _, _) | ForallRightRule(_, _, _, _, _) =>
      throw new HerbrandExtractionException("ERROR: Found strong quantifier rule while extracting Herbrand sequent.")

    case CutRule(_, _, _, _, _) => throw new HerbrandExtractionException("ERROR: Found cut rule while extracting Herbrand sequent.")
  }

}