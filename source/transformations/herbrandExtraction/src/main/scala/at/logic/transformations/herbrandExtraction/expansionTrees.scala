package at.logic.transformations.herbrandExtraction

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.language.hol._
import at.logic.utils.ds.algebraic.trees._
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier => WQTree, StrongQuantifier => SQTree, And => AndTree, Or => OrTree, Imp => ImpTree,
Not => NotTree, Atom => AtomTree}
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.occurrences._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.Var

object extractExpansionTrees {

  def apply(proof: LKProof): Tuple2[Seq[ExpansionTree],Seq[ExpansionTree]] = {
    val map = extract(proof)
    (proof.root.antecedent.map(fo => map(fo)), proof.root.succedent.map(fo => map(fo)))
  }

  private def extract(proof: LKProof): Map[FormulaOccurrence,ExpansionTree] = proof match {
    case Axiom(r) => Map(r.antecedent.map(fo => (fo,AtomTree(fo.formula))) ++
                         r.succedent.map(fo => (fo, AtomTree(fo.formula))): _*)
    case UnaryLKProof(_,up,r,_,p) => {
      val map = extract(up)
      getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map) + Pair(p, (proof match {
        case WeakeningRightRule(_,_,_) => AtomTree(p.formula)
        case WeakeningLeftRule(_,_,_) => AtomTree(p.formula)
        case ForallLeftRule(_,_,a,_,t) => WQTree(p.formula, List(Pair(map(a),t)))
        case ExistsRightRule(_,_,a,_,t) => WQTree(p.formula, List(Pair(map(a),t)))
        case ForallRightRule(_,_,a,_,v) => SQTree(p.formula, v, map(a))
        case ExistsLeftRule(_,_,a,_,v) => SQTree(p.formula, v, map(a))
        case ContractionLeftRule(_,_,a1,a2,_) => mergeTrees(map(a1),map(a2))
        case ContractionRightRule(_,_,a1,a2,_) => mergeTrees(map(a1),map(a2))
        case AndLeft1Rule(_,_,a,_) => {val And(_,f2) = p.formula; AndTree(map(a), AtomTree(f2))}
        case AndLeft2Rule(_,_,a,_) => {val And(f1,_) = p.formula; AndTree(AtomTree(f1),map(a))}
        case OrRight1Rule(_,_,a,_) => {val Or(_,f2) = p.formula; OrTree(map(a), AtomTree(f2))}
        case OrRight2Rule(_,_,a,_) => {val Or(f1,_) = p.formula; OrTree(AtomTree(f1),map(a))}
        case ImpRightRule(_,_,a1,a2,_) => ImpTree(map(a1),map(a2))
        case NegLeftRule(_,_,a,_) => NotTree(map(a))
        case NegRightRule(_,_,a,_) => NotTree(map(a))
      }))
    }
    case CutRule(up1,up2,r,_,_) => getMapOfContext((r.antecedent ++ r.succedent).toSet, extract(up1) ++ extract(up2))
    case BinaryLKProof(_,up1,up2,r,a1,a2,Some(p)) => {
      val map = extract(up1) ++ extract(up2)
      getMapOfContext((r.antecedent ++ r.succedent).toSet - p, map) + Pair(p, (proof match {
        case ImpLeftRule(_,_,_,_,_,_) => ImpTree(map(a1),map(a2))
        case OrLeftRule(_,_,_,_,_,_) => OrTree(map(a1),map(a2))
        case AndRightRule(_,_,_,_,_,_) => AndTree(map(a1),map(a2))
        case EquationLeft1Rule(_,_,_,_,_,_) => map(a2)
        case EquationLeft2Rule(_,_,_,_,_,_) => map(a2)
        case EquationRight1Rule(_,_,_,_,_,_) => map(a2)
        case EquationRight2Rule(_,_,_,_,_,_) => map(a2)
      }))
    }
    case _ => throw new IllegalArgumentException("unsupported proof rule: " + proof)
  }

  // the set of formula occurrences given to method must not contain any principal formula
  private def getMapOfContext(s: Set[FormulaOccurrence], map: Map[FormulaOccurrence,ExpansionTree]): Map[FormulaOccurrence,ExpansionTree] =
    Map(s.toList.map(fo => (fo, {
      require(fo.ancestors.size == 1)
      map(fo.ancestors.head)
    })): _*)

  // The trees must have the same nodes up to quantified terms except a none terminal node in one tree can be terminal in the other
  private def mergeTrees(tree1: ExpansionTree, tree2: ExpansionTree): ExpansionTree = {
    if (tree1.isInstanceOf[AtomTree] && !(tree2.isInstanceOf[AtomTree])) tree2
    else if (tree2.isInstanceOf[AtomTree]) tree1
    else (tree1,tree2) match {
      case (SQTree(_,_,_),SQTree(_,_,_)) => throw new UnsupportedOperationException("Expansion tree extractions works for skolemized proofs only(for now)")
      case (WQTree(f1, children1), WQTree(f2,children2)) if f1 == f2 => WQTree(f1, setAddition(children1,children2))
      case (NotTree(s1),NotTree(s2)) => NotTree(mergeTrees(s1,s2))
      case (AndTree(s1,t1),AndTree(s2,t2)) => AndTree(mergeTrees(s1,s2),mergeTrees(t1,t2))
      case (OrTree(s1,t1),OrTree(s2,t2)) => OrTree(mergeTrees(s1,s2),mergeTrees(t1,t2))
      case (ImpTree(s1,t1),ImpTree(s2,t2)) => ImpTree(mergeTrees(s1,s2),mergeTrees(t1,t2))
      case _ => throw new IllegalArgumentException("Bug in mergeTrees in extractExpansionTrees. By Construction, the trees to be merge should have the same structure, which is violated.")
    }
  }

  private def setAddition(children1 : Seq[Tuple2[ExpansionTree,HOLExpression]], children2: Seq[Tuple2[ExpansionTree,HOLExpression]]):
  Seq[Tuple2[ExpansionTree,HOLExpression]] = {
    val sorted = (children1 ++ children2).sortWith((e1,e2) => e1._2.toString > e2._2.toString)
    sorted.foldLeft(List[Tuple2[ExpansionTree,HOLExpression]]())((ls,e1) => ls match {
      case Nil => List(e1)
      case (t2,e2):: _ if e1._2 == e2 => ls
      case _ =>  e1 :: ls
    })
  }
}
