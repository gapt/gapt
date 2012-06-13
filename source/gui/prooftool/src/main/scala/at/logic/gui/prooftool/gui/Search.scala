package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/21/12
 * Time: 12:41 PM
 */

import at.logic.calculi.treeProofs.TreeProof
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base.{BinaryLKProof, UnaryLKProof, NullaryLKProof}
import at.logic.utils.ds.trees.{BinaryTree, UnaryTree, LeafTree, Tree}
import at.logic.language.hol.HOLExpression


object Search {

  def inTreeProof(str: String, proof: TreeProof[_]): Set[FormulaOccurrence] = proof match {
    case p: NullaryLKProof =>
      ( p.root.antecedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ++
        p.root.succedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ).toSet
    case p: UnaryLKProof =>
      inTreeProof(str, p.uProof.asInstanceOf[TreeProof[_]]) ++
        ( p.root.antecedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ++
          p.root.succedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ).toSet
    case p: BinaryLKProof =>
      inTreeProof(str, p.uProof1.asInstanceOf[TreeProof[_]]) ++
      inTreeProof(str, p.uProof2.asInstanceOf[TreeProof[_]]) ++
        ( p.root.antecedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ++
          p.root.succedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ).toSet
    case _ => throw new Exception("Can not search in this object!")
  }
 /*
  def inTree(str: String, tree: Tree[_]): Set[FormulaOccurrence] = tree match {
    case p: LeafTree => p.vertex match {
      case he: HOLExpression =>
    }
      ( p.root.antecedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ++
        p.root.succedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ).toSet
    case p: UnaryTree =>
      inTree(str, p.t) ++
        ( p.root.antecedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ++
          p.root.succedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ).toSet
    case p: BinaryTree =>
      inTree(str, p.t1) ++ inTree(str, p.t2) ++
        ( p.root.antecedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ++
          p.root.succedent.filter( fo => DrawSequent.formulaToLatexString(fo.formula).contains(str)) ).toSet
  } */
}
