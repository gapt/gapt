package at.logic.transformations.ceres

import at.logic.calculi.resolution.FClause
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.hol._

import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk._
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof

import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.algorithms.lk.{addWeakenings, applySubstitution}
import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithmHOL

import at.logic.transformations.ceres.projections.Projections


/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/10/13
 * Time: 7:11 PM
 * To change this template use File | Settings | File Templates.
 */

object CERESR2LK {
  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param endsequent The end-sequent of the original proof
   * @param proj The projections of the original proof
   * @param rp A resolution refutation
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply(endsequent : FSequent, proj : Set[LKProof], rp : RobinsonResolutionProof) = {
    RobinsonToLK(rp, endsequent, fc => CERES.findMatchingProjection(endsequent, proj)(fc.toFSequent))
  }
}

object CERES {
  //TODO: this works for classical CERES only
  def apply(lkproof : LKProof, refutation: LKProof, pred : HOLFormula => Boolean) : LKProof = {
    CERES(lkproof.root.toFSequent(), Projections(lkproof), refutation)
  }

  /**
   * Applies the CERES method to a first order proof with equality.
   * @param endsequent The end-sequent of the original proof
   * @param projections The projections of the original proof
   * @param refutation A resolution refutation converted to LK (for instance with Robinson2LK)
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply(endsequent : FSequent, projections : Set[LKProof], refutation: LKProof) : LKProof = refutation match {
    case Axiom(root) =>
      findMatchingProjection(endsequent, projections)(root.toFSequent())

    case CutRule(p1,p2,root,aux1,aux2) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      contractEndsequent(CutRule(rp1,rp2,aux1.formula), endsequent)

    case ContractionLeftRule(p1,root,aux1,aux2,_) =>
      val rp1 = CERES(endsequent, projections, p1)
      ContractionLeftRule(rp1,aux1.formula)
    case ContractionRightRule(p1,root,aux1,aux2,_) =>
      val rp1 = CERES(endsequent, projections, p1)
      ContractionRightRule(rp1,aux1.formula)

    case WeakeningLeftRule(p1,root,aux1) =>
      val rp1 = CERES(endsequent, projections, p1)
      WeakeningLeftRule(rp1,aux1.formula)
    case WeakeningRightRule(p1,root,aux1) =>
      val rp1 = CERES(endsequent, projections, p1)
      WeakeningRightRule(rp1,aux1.formula)

    case EquationLeft1Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      contractEndsequent(EquationLeft1Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula), endsequent)
    case EquationLeft2Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      contractEndsequent(EquationLeft2Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula), endsequent)
    case EquationRight1Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      contractEndsequent(EquationRight1Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula), endsequent)
    case EquationRight2Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      contractEndsequent(EquationRight2Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula), endsequent)

    case _ =>
      throw new Exception("Refutation is expected to contain only cut, contraction and equality rules!")

  }

  def findMatchingProjection(endsequent : FSequent, projections : Set[LKProof]) : (FSequent => LKProof) = {
    (axfs: FSequent) => {
      projections.find(x => StillmanSubsumptionAlgorithmHOL.subsumes(x.root.toFSequent() diff endsequent, axfs)) match {
        case None => throw new Exception("Could not find a projection to " + axfs + " in " +
          projections.map(_.root).mkString("{\n", ",\n", "\n}"))
        case Some(proj) =>
          val Some(sub) = StillmanSubsumptionAlgorithmHOL.subsumes_by(proj.root.toFSequent() diff endsequent, axfs)
          val (subproj, _) = applySubstitution(proj, sub)
          require((subproj.root.toFSequent diff endsequent).multiSetEquals(axfs),
            "Instance of projection with end-sequent " + subproj.root + " is not equal to " + axfs + " x " + endsequent)
          subproj
      }
    }
  }

  def refProjection(es : FSequent) : LKProof = {
    require(es.formulas.nonEmpty, "Can not project reflexivity to an empty end-sequent!")
    val x = es.formulas(0).factory.createVar(StringSymbol("x"), Ti).asInstanceOf[HOLVar]
    val axiomseq = FSequent(Nil, List(Equation(x,x)))
    addWeakenings(Axiom(axiomseq.antecedent, axiomseq.succedent), axiomseq compose es)
  }

  def contractEndsequent(p : LKProof, es : FSequent) = {
    val left = es.antecedent.foldLeft(p)( (proof, f) => ContractionLeftRule(proof, f))
    val right = es.succedent.foldLeft(left)( (proof, f) => ContractionRightRule(proof, f))
    right
  }


}

