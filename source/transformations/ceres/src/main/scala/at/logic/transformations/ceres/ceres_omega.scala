package at.logic.transformations.ceres

import at.logic.calculi.lk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol.Equation
import at.logic.language.lambda.types.Ti
import at.logic.transformations.ceres.struct.Struct
import at.logic.utils.dssupport.ListSupport._
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.lksk.{ Axiom => LKSKAxiom, _}
import at.logic.calculi.resolution.ral._

/**
 * Created by marty on 10/6/14.
 */
object ceres_omega {
  def apply(projections : Set[LKProof], ralproof : RalResolutionProof[LabelledSequent], es : LabelledSequent, struct : Struct) : (LKProof, LabelledSequent) = ralproof match {
    //reflexivity as initial rule
    case InitialSequent( s@LabelledSequent(Nil, List(LabelledFormulaOccurrence(Equation(x,y), anc, label)) ))
       if (x==y) && (x.exptype == Ti) =>

      val (rule,_) = LKSKAxiom.createDefault(s.toFSequent, (List(), List(label)))

      (rule, LabelledSequent(Nil,Nil))


    case InitialSequent(root ) =>
      projections.find(x => {
        def removeAll(l1:List[LabelledFormulaOccurrence], l2:List[LabelledFormulaOccurrence]) = {
          l1.foldLeft(l2)( (list,fo) => removeFirstWhere(list, (x:LabelledFormulaOccurrence) =>
            x.formula==fo.formula && x.skolem_label == fo.skolem_label))
        }

        val pes = filterEndsequent(x.root.asInstanceOf[LabelledSequent], es, struct)
        val containsallante = removeAll(pes.l_antecedent.toList,root.l_antecedent.toList)
        val containsallsucc = removeAll(pes.l_succedent.toList,root.l_succedent.toList)
        val containsallante_ = removeAll(root.l_antecedent.toList,pes.l_antecedent.toList)
        val containsallsucc_ = removeAll(root.l_succedent.toList,pes.l_succedent.toList)

        (containsallante ++ containsallsucc ++ containsallante_ ++ containsallsucc_).isEmpty
      }) match {
        case Some(proof) => (proof, filterEndsequent(proof.root.asInstanceOf[LabelledSequent], es, struct))
        case None =>
          throw new Exception("Could not find a projection for the clause "+root+" in "+projections.map(_.root))
      }

    case Cut(root, parent1, parent2, p1occs, p2occs) =>
      val (lkparent1, clause1) = ceres_omega(projections, parent1, es, struct)
      val (lkparent2, clause2) = ceres_omega(projections, parent2, es, struct)
      val leftcutformulas = p1occs.foldLeft(List[LabelledFormulaOccurrence]())( (list, fo) => findAuxByFormulaAndLabel(fo.asInstanceOf[LabelledFormulaOccurrence], clause1.l_succedent, list) :: list ).reverse
      val rightcutformulas = p2occs.foldLeft(List[LabelledFormulaOccurrence]())( (list, fo) => findAuxByFormulaAndLabel(fo.asInstanceOf[LabelledFormulaOccurrence], clause2.l_antecedent, list) :: list ).reverse
      val (c1,caux1, c2, caux2) = (leftcutformulas, rightcutformulas) match {
        case (x::xs, y::ys) => (x,xs,y,ys)
        case (Nil, _) => throw new Exception("Could not find the cut formula "+p1occs(0).formula+" in left parent "+lkparent1.root)
        case (_, Nil) => throw new Exception("Could not find the cut formula "+p2occs(0).formula+" in right parent "+lkparent2.root)
      }

      val cleft = caux1.foldLeft(lkparent1)((proof, occ) =>
        ContractionRightRule(proof, pickFOWithAncestor(proof.root.succedent,c1), pickFOWithAncestor(proof.root.succedent, occ )) )
      val cright = caux1.foldLeft(lkparent2)((proof, occ) =>
        ContractionLeftRule(proof, pickFOWithAncestor(proof.root.antecedent,c2), pickFOWithAncestor(proof.root.antecedent, occ )) )

      val rule = CutRule(cleft, cright, pickFOWithAncestor(cleft.root.succedent, c1), pickFOWithAncestor(cright.root.antecedent, c2))
      val nclauses = filterByAncestor(rule.root.asInstanceOf[LabelledSequent], clause1 compose clause2)
      (rule, nclauses)

    case AFactorF(root, parent, contr, aux, _) =>
      val (lkparent, clause1) = ceres_omega(projections, parent, es, struct)
      val c1 = findAuxByFormulaAndLabel(contr, clause1.l_antecedent, Nil)
      val c2 = findAuxByFormulaAndLabel(contr, clause1.l_antecedent, c1::Nil)
      val rule = ContractionLeftRule(lkparent, c1, c2)
      val nclauses = filterByAncestor(rule.root.asInstanceOf[LabelledSequent], clause1)
      (rule, nclauses)

    case AFactorT(root, parent, contr, aux, _) =>
      val (lkparent, clause1) = ceres_omega(projections, parent, es, struct)
      val c1 = findAuxByFormulaAndLabel(contr, clause1.l_succedent, Nil)
      val c2 = findAuxByFormulaAndLabel(contr, clause1.l_succedent, c1::Nil)
      val rule = ContractionRightRule(lkparent, c1, c2)
      val nclauses = filterByAncestor(rule.root.asInstanceOf[LabelledSequent], clause1)
      (rule, nclauses)


    case ParaF(root, parent1, parent2, p1occ, p2occ, principial, flipped) =>
      val (lkparent1, clause1) = ceres_omega(projections, parent1, es, struct)
      val (lkparent2, clause2) = ceres_omega(projections, parent2, es, struct)
      val eqn : FormulaOccurrence = findAuxByFormulaAndLabel(p1occ, clause1.l_succedent, Nil)
      val modulant : FormulaOccurrence = findAuxByFormulaAndLabel(p2occ.asInstanceOf[LabelledFormulaOccurrence], clause2.l_antecedent, Nil)
      val rule = if (!flipped) EquationLeft1Rule(lkparent1, lkparent2, eqn, modulant, principial.formula) else EquationLeft2Rule(lkparent1, lkparent2, eqn, modulant, principial.formula)
      val nclauses = filterByAncestor(rule.root.asInstanceOf[LabelledSequent], clause1 compose clause2)
      (rule, nclauses)

    case ParaT(root, parent1, parent2, p1occ, p2occ, principial, flipped) =>
      val (lkparent1, clause1) = ceres_omega(projections, parent1, es, struct)
      val (lkparent2, clause2) = ceres_omega(projections, parent2, es, struct)
      val eqn : FormulaOccurrence = findAuxByFormulaAndLabel(p1occ, clause1.l_succedent, Nil)
      val modulant : FormulaOccurrence = findAuxByFormulaAndLabel(p2occ.asInstanceOf[LabelledFormulaOccurrence], clause2.l_succedent, Nil)
      val rule = if (!flipped) EquationRight1Rule(lkparent1, lkparent2, eqn, modulant, principial.formula) else EquationRight2Rule(lkparent1, lkparent2, eqn, modulant, principial.formula)
      val nclauses = filterByAncestor(rule.root.asInstanceOf[LabelledSequent], clause1 compose clause2)
      (rule, nclauses)


    case _ => throw new Exception("Unhandled case: "+ralproof)
  }


  def filterByAncestor(root:LabelledSequent, anc : LabelledSequent) : LabelledSequent = LabelledSequent(
    root.l_antecedent.filter(x => anc.l_antecedent.exists(y => tranAncestors(x).contains(y))),
    root.l_succedent.filter(x => anc.l_succedent.exists(y => tranAncestors(x).contains(y)))
  )

  def findAuxByFormulaAndLabel(aux : LabelledFormulaOccurrence, candidates : Seq[LabelledFormulaOccurrence], exclusion_list : Seq[LabelledFormulaOccurrence]) =
    findAux(aux, candidates, x => x.skolem_label == aux.skolem_label && x.formula == aux.formula, exclusion_list)

  def findAux(aux : LabelledFormulaOccurrence, candidates : Seq[LabelledFormulaOccurrence], pred : LabelledFormulaOccurrence => Boolean, exclusion_list : Seq[LabelledFormulaOccurrence]) =
  candidates.diff(exclusion_list).find(pred) match {
    case Some(fo) => fo
    case None => throw new Exception("Could not find a candidate for "+aux+" in "+candidates.mkString(", ")+exclusion_list.mkString(" ignoring: ",", ","."))
  }

  /* TODO: this might not work if we have atom formulas in the end-sequent. then a formula which comes from a weakining
     might remain and in case of subsequent substitutions, the formula decomposition steps could fail, since they expect
     an introduction rule A :- A */
  def filterEndsequent(root : LabelledSequent, es : LabelledSequent, struct : Struct) = LabelledSequent(
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
