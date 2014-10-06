package at.logic.transformations.ceres

import at.logic.calculi.lk.{CutRule, ContractionLeftRule, ContractionRightRule}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.utils.dssupport.ListSupport._
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.lksk.{LabelledFormulaOccurrence, LabelledSequent}
import at.logic.calculi.resolution.ral._

/**
 * Created by marty on 10/6/14.
 */
object ceres_omega {
  def apply(projections : Set[LKProof], ralproof : RalResolutionProof[LabelledSequent], es : LabelledSequent) : LKProof = ralproof match {
    case Cut(root, parent1, parent2, p1occs, p2occs) =>
      val lkparent1 = ceres_omega(projections, parent1, es)
      val lkparent2 = ceres_omega(projections, parent2, es)
      val clause1 = filterEndsequent(lkparent1.root.asInstanceOf[LabelledSequent], es)
      val clause2 = filterEndsequent(lkparent2.root.asInstanceOf[LabelledSequent], es)
      val (c1::caux1) = clause1.succedent
      val (c2::caux2) = clause2.succedent
      val cleft = caux1.foldLeft(lkparent1)((proof, occ) =>
        ContractionRightRule(proof, pickFOWithAncestor(proof.root.succedent,c1), pickFOWithAncestor(proof.root.succedent, occ )) )
      val cright = caux1.foldLeft(lkparent2)((proof, occ) =>
        ContractionLeftRule(proof, pickFOWithAncestor(proof.root.antecedent,c2), pickFOWithAncestor(proof.root.antecedent, occ )) )

      val rule = CutRule(cleft, cright, pickFOWithAncestor(cleft.root.succedent, c1), pickFOWithAncestor(cright.root.antecedent, c2))
      rule


    case _ => throw new Exception("Unhandled case: "+ralproof)
  }

  /* TODO: this might not work if we have atom formulas in the end-sequent. then a formula which comes from a weakining
     might remain and in case of subsequent substitutions, the formula decomposition steps could fail, since they expect
     an introduction rule A :- A */
  def filterEndsequent(root : LabelledSequent, es : LabelledSequent) = LabelledSequent(
    es.antecedent.foldLeft(root.l_antecedent.toList)( (list, fo) => removeFirstWhere(list, (x:LabelledFormulaOccurrence) => fo.formula == x.formula)  ),
    es.succedent.foldLeft(root.l_succedent.toList)( (list, fo) => removeFirstWhere(list, (x:LabelledFormulaOccurrence) => fo.formula == x.formula)  )
  )

  def tranAncestors(fo : FormulaOccurrence) : List[FormulaOccurrence] = {
    fo :: fo.ancestors.toList.flatMap(x => tranAncestors(x))
  }

  def tranAncestors(fo : LabelledFormulaOccurrence) : List[LabelledFormulaOccurrence] = {
    fo :: fo.ancestors.flatMap(x => tranAncestors(x))
  }


  def pickFOWithAncestor(l : Seq[FormulaOccurrence], anc : FormulaOccurrence) = l.find(x => tranAncestors(x).contains(anc)) match {
    case Some(a) => a
    case None => throw new Exception("Could not find any occurrence with ancestor "+anc+" in "+l)
  }


  def pickFOWithAncestor(l : Seq[LabelledFormulaOccurrence], anc : LabelledFormulaOccurrence) = l.find(x => tranAncestors(x).contains(anc)) match {
    case Some(a) => a
    case None => throw new Exception("Could not find any occurrence with ancestor "+anc+" in "+l)
  }


}
