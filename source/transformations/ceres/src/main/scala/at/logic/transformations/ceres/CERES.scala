package at.logic.transformations.ceres

import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof
import at.logic.transformations.ceres.projections.Projections
import at.logic.calculi.resolution.FClause
import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.algorithms.lk.CloneLKProof
import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.language.hol.logicSymbols._
import at.logic.algorithms.matching.NaiveIncompleteMatchingAlgorithm
import at.logic.language.lambda.{App, LambdaExpression, Var}
import at.logic.language.lambda.types.{TA, ->, Ti, To}
import at.logic.language.lambda.symbols._
import scala.Some
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.To
import at.logic.calculi.lk.base.FSequent
import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithmHOL
import at.logic.algorithms.lksk.applySubstitution
import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/10/13
 * Time: 7:11 PM
 * To change this template use File | Settings | File Templates.
 */
object CERES {
  //TODO: fix direct computation of proof in Robinson2LK
  //TODO: this works for CERESw and classical CERES, not CERESs
  //TODO: add memoization for duplicated derivations

  def extractSubstititions(rp : RobinsonResolutionProof, lkproof : LKProof, proj : Set[LKProof]) = {
    val es = lkproof.root.toFSequent()
    RobinsonToLK(rp, es, (c => Axiom(c.neg, c.pos)))


    val pes = proj.map(_.root.toFSequent())
    val lkres = pes.map(p => {
      val clause = p.diff(es)
    })

  }

  def apply(lkproof : LKProof, refutation: LKProof, pred : HOLFormula => Boolean) : LKProof = {


    CERES(lkproof.root.toFSequent(), Projections(lkproof), refutation)
  }

  def apply(endsequent : FSequent, projections : Set[LKProof], refutation: LKProof) : LKProof = refutation match {
    case Axiom(root) =>
      val axfs = root.toFSequent()
      projections.find(x => StillmanSubsumptionAlgorithmHOL.subsumes(x.root.toFSequent(),axfs) ) match {
        case None => throw new Exception("Could not find a projection to "+axfs+" in "+
                                          projections.map(_.root).mkString("{\n",",\n","\n}"))
        case Some(proj) =>
          val Some(sub) = StillmanSubsumptionAlgorithmHOL.subsumes_by(proj.root.toFSequent(), axfs)
          val (subproj,_) = applySubstitution(proj,sub)
          require(subproj.root.toFSequent.multiSetEquals(axfs),
                  "Instance of projection with end-sequent "+subproj.root+" is not equal to "+axfs )
          subproj
      }


    case CutRule(p1,p2,root,aux1,aux2) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      CutRule(rp1,rp2,aux1.formula)

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
      EquationLeft1Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula)
    case EquationLeft2Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      EquationLeft2Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula)
    case EquationRight1Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      EquationRight1Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula)
    case EquationRight2Rule(p1,p2,root,aux1,aux2,main) =>
      val rp1 = CERES(endsequent, projections, p1)
      val rp2 = CERES(endsequent, projections, p2)
      EquationRight2Rule(rp1,rp2,aux1.formula,aux2.formula,main.formula)

    case _ =>
      throw new Exception("Refutation is expected to contain only cut, contraction and equality rules!")



  }

}

