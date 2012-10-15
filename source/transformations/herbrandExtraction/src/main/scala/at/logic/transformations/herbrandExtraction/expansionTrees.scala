package at.logic.transformations.herbrandExtraction

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.hol._
import at.logic.utils.ds.algebraic.trees._
import at.logic.utils.ds.trees.TreeA
import at.logic.calculi.lk.lkExtractors._
import scala.collection.immutable.Map
import at.logic.calculi.occurrences._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.Var

object extractExpansionTrees {

  type V = HOLFormula
  type E = Option[Tuple2[HOLExpression,Boolean]]
  type TreeType = Tree[V,E]
  type TreeTypeA = TreeA[V,E]

  def apply(proof: LKProof): Tuple2[Seq[TreeTypeA],Seq[TreeTypeA]] = {
    val map = extract(proof)
    (proof.root.antecedent.map(fo => map(fo)), proof.root.succedent.map(fo => map(fo)))
  }

  private def extract(proof: LKProof): Map[FormulaOccurrence,TreeType] = proof match {
    case Axiom(r) => Map(r.antecedent.map(fo => (fo, TerminalNode[V,E](fo.formula))) ++
                         r.succedent.map(fo => (fo, TerminalNode[V,E](fo.formula))): _*)
    case WeakeningRightRule(up,r,p) => {
      val map = extract(up)
      (getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map) + Pair(p, TerminalNode[V,E](p.formula)))
    }
    case WeakeningLeftRule(up,r,p) => {
      val map = extract(up)
      getMapOfContext((r.antecedent ++ r.succedent).toSet - p,map) + Pair(p, TerminalNode[V,E](p.formula))
    }
    case ForallLeftRule(up,r,a,p,st) => handleQuantifier(up,r,a,p,st,false)
    case ExistsRightRule(up,r,a,p,st) => handleQuantifier(up,r,a,p,st,false)
    case ForallRightRule(up,r,a,p,st) => handleQuantifier(up,r,a,p,st,true)
    case ExistsLeftRule(up,r,a,p,st) => handleQuantifier(up,r,a,p,st,true)
    case ContractionLeftRule(up,r,a1,a2,p) => handleContraction(up,r,a1,a2,p)
    case ContractionRightRule(up,r,a1,a2,p) => handleContraction(up,r,a1,a2,p)
    case AndLeft1Rule(up,r,a,p) => {val And(_,f2) = p.formula; handleBinarySymbolInUnaryRule1(up,r,a,p,f2)}
    case AndLeft2Rule(up,r,a,p) => {val And(f1,_) = p.formula; handleBinarySymbolInUnaryRule2(up,r,a,p,f1)}
    case OrRight1Rule(up,r,a,p) => {val Or(_,f2) = p.formula; handleBinarySymbolInUnaryRule1(up,r,a,p,f2)}
    case OrRight2Rule(up,r,a,p) => {val Or(f1,_) = p.formula; handleBinarySymbolInUnaryRule2(up,r,a,p,f1)}
    // missing rule ImpRight since it has 2 aux formulas
    case UnaryLKProof(_,up,r,al,p) if (al.size == 1) => {
      val map = extract(up)
      val o = al.head
      getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map) + Pair(p, NoneTerminalNode[V,E](p.formula, List((map(o),None))))
    }
    // deal with ImpRight
    case ImpRightRule(up,r,a1,a2,p) => {
      val map = extract(up)
      getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map) + Pair(p, NoneTerminalNode[V,E](p.formula, List((map(a1),None),(map(a2),None))))
    }
    case BinaryLKProof(_,up1,up2,r,a1,a2,sp) => {
      val map = extract(up1) ++ extract(up2)
      if (sp == None) getMapOfContext(r,map)
      else getMapOfContext((r.antecedent ++ r.succedent).toSet - sp.get, map) + Pair(sp.get, NoneTerminalNode[V,E](sp.get.formula,
        List((map(a1),None),(map(a2),None))))
    }
  }

  private def handleContraction(proof: LKProof, r: Sequent, a1: FormulaOccurrence, a2: FormulaOccurrence, p: FormulaOccurrence) = {
    val map = extract(proof)
    val expTree = mergeTrees(map(a1),map(a2))
    getMapOfContext((r.antecedent ++ r.succedent).toSet - p,map) + Pair(p, expTree)
  }

  private def handleBinarySymbolInUnaryRule1(proof: LKProof, r: Sequent, ao: FormulaOccurrence, po: FormulaOccurrence, f: HOLFormula) = {
    val map = extract(proof)
    getMapOfContext((r.antecedent ++ r.succedent).toSet - po,map) + Pair(po, NoneTerminalNode[V,E](po.formula,
      List((map(ao),None),(TerminalNode[V,E](f),None))))
  }

  private def handleBinarySymbolInUnaryRule2(proof: LKProof, r: Sequent, ao: FormulaOccurrence, po: FormulaOccurrence, f: HOLFormula) = {
    val map = extract(proof)
    getMapOfContext((r.antecedent ++ r.succedent).toSet - po,map) + Pair(po, NoneTerminalNode[V,E](po.formula,
      List((TerminalNode[V,E](f),None),(map(ao),None))))
  }

  private def handleQuantifier(proof: LKProof, r: Sequent, ao: FormulaOccurrence, po: FormulaOccurrence, t: HOLExpression, eigenvar:
    Boolean): Map[FormulaOccurrence,TreeType] = {
    val map = extract(proof)
    getMapOfContext((r.antecedent ++ r.succedent).toSet - po, map) + Pair(po, NoneTerminalNode[V,E](po.formula,
      List((map(ao),Some(Pair(t,eigenvar))))))
  }

  private def getMapOfContext(r: Sequent, map: Map[FormulaOccurrence,TreeType]): Map[FormulaOccurrence,TreeType] =
    getMapOfContext((r.antecedent ++ r.succedent).toSet, map)

  // the set of formula occurrences given to method must not contain any principal formula
  private def getMapOfContext(s: Set[FormulaOccurrence], map: Map[FormulaOccurrence,TreeType]): Map[FormulaOccurrence,TreeType] =
    Map(s.toList.map(fo => (fo, {
      require(fo.ancestors.size == 1)
      map(fo.ancestors.head)
    })): _*)

  // The trees must have the same nodes up to quantified terms except a none terminal node in one tree can be terminal in the other
  private def mergeTrees(tree1: TreeType, tree2: TreeType): TreeType = {
    require(tree1.node == tree2.node)
    if (tree1.isInstanceOf[TerminalNode[_,_]] && !(tree2.isInstanceOf[TerminalNode[_,_]])) tree2
    else if (tree2.isInstanceOf[TerminalNode[_,_]]) tree1
    else {
      val nt1 = tree1.asInstanceOf[NoneTerminalNode[V,E]]
      val nt2 = tree2.asInstanceOf[NoneTerminalNode[V,E]]
      tree1.node match {
        case Quantifier(_,x,p) => {
          val (stree1,Some((term1,isEigenvar))) = nt1.parents.head
          val (stree2, Some((term2,_))) = nt2.parents.head
          if (isEigenvar) NoneTerminalNode[V,E](tree1.node,
            List((mergeTrees(stree1,applySubInTree(Substitution(term2.asInstanceOf[Var],term1),stree2)),Some(term1,true))))
          else NoneTerminalNode[V,E](tree1.node, (nt1.parents ++ nt2.parents)) // TOFIX we do not apply it recursively
        }
        case Neg(f) => NoneTerminalNode[V,E](tree1.node, List((mergeTrees(nt1.parents.head._1,nt2.parents.head._1),None)))
        case BinaryFormula(f1,f2) => NoneTerminalNode[V,E](tree1.node,
          List((mergeTrees(nt1.parents.head._1,nt2.parents.head._1),None),(mergeTrees(nt1.parents.tail.head._1,nt2.parents.tail.head._1),None)))
      }
    }
  }

  private def applySubInTree(sub: Substitution[HOLExpression], tree: TreeType): TreeType = tree match {
    case TerminalNode(f) => TerminalNode[V,E](sub(f).asInstanceOf[V])
    case NoneTerminalNode(f,parents) => NoneTerminalNode(sub(f).asInstanceOf[V], parents.map(param => (applySubInTree(sub,param._1),param._2)))
  }
}
