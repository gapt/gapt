package at.logic.calculi.expansionTrees

import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, Neg => NegHOL, _}
import at.logic.utils.ds.trees._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.matching.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.types.FSequent
import scala.collection.mutable.ListBuffer


/**
 * General class for expansion trees with pseudo case classes including for MergeNodes, which only occur during merging/substituting
 */
trait ExpansionTreeWithMerges extends TreeA[Option[HOLFormula],Option[HOLExpression]] {
  override def toString() = this match {
    case Atom(f) => f.toString
    case Neg(t1) => NegSymbol + t1.toString
    case And(t1,t2) => t1.toString + AndSymbol + t2.toString
    case Or(t1,t2) => t1.toString + OrSymbol + t2.toString
    case Imp(t1,t2) => t1.toString + OrSymbol + t2.toString
    case WeakQuantifier(formula,children) => "WeakQuantifier("+formula+", "+children+")"
    case StrongQuantifier(formula, variable, selection) => "StrongQuantifier("+formula+", "+variable+", "+selection+")"
    case MergeNode(left, right) => "MergeNode("+left+", "+right+")"
    case _ => throw new Exception("Unhandled case in ExpanstionTreeWithMerges.toString")
  }
}


/**
 * Feigns being a subclass of ExpansionTreeWithMerges.
 * The apply methods in the pseudo case classes return ETs in case the arguments forming the children are ETs.
 * As the children are immutable, this ensures that the tree does not contain merges.
 * The classes also contain methods that have ETs as formal input and output parameters, which eliminates the need for
 * a lot of casting in client code.
 */
trait ExpansionTree extends ExpansionTreeWithMerges {
}

// generic equality for trees solely defined by node and children
trait NonTerminalNodeAWithEquality[+V, +E] extends NonTerminalNodeA[V, E] {
  override def equals(obj: scala.Any): Boolean =
    (this.getClass == obj.getClass) &&
    (this.node equals obj.asInstanceOf[NonTerminalNodeA[V, E]].node) &&
    (this.children equals obj.asInstanceOf[NonTerminalNodeA[V, E]].children)
}
trait TerminalNodeAWithEquality[+V, +E] extends TerminalNodeA[V, E] {
  override def equals(obj: scala.Any): Boolean =
    (this.getClass == obj.getClass) &&
    (this.node equals obj.asInstanceOf[TerminalNodeA[V, E]].node)
}

/**
 * Represents Qx A +u1 E_1 ... +u_n E_n this way:
 * @param formula A
 * @param instances [ (E_1, u_1), ... , (E_n, u_1)
 */
class WeakQuantifier(val formula: HOLFormula, val instances: Seq[(ExpansionTreeWithMerges, HOLExpression)])
  extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = instances.map(x => (x._1,Some(x._2)))
}
object WeakQuantifier {
  // can't have another apply for ExpansionTree as type info gets lost with type erasure
  def apply(formula: HOLFormula, instances: Seq[(ExpansionTreeWithMerges, HOLExpression)]) =
    if (instances.forall({case (et, _) => et.isInstanceOf[ExpansionTree] }))  new WeakQuantifier(formula, instances) with ExpansionTree
    else new WeakQuantifier(formula, instances)
  def unapply(et: ExpansionTreeWithMerges) = et match {
    case weakQuantifier : WeakQuantifier => Some( (weakQuantifier.formula, weakQuantifier.instances) )
    case _ => None
  }
  def unapply(et: ExpansionTree): Option[(HOLFormula, Seq[(ExpansionTree, HOLExpression)])] = et match {
    case weakQuantifier : WeakQuantifier => Some( (weakQuantifier.formula, weakQuantifier.instances.asInstanceOf[Seq[(ExpansionTree, HOLExpression)]] ) )
    case _ => None
  }
}


/**
 * Represents Qx A +u E:
 * @param formula A
 * @param variable u
 * @param selection E
 */
protected[expansionTrees] class StrongQuantifier(val formula: HOLFormula, val variable: HOLVar, val selection: ExpansionTreeWithMerges)
  extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = List(Pair(selection,Some(variable)))
}
object StrongQuantifier {
  def apply(formula: HOLFormula, variable: HOLVar, selection: ExpansionTree): ExpansionTree =
    // NOTE: this statement must not occur again in the other apply as it creates an own, distinct class, which scala treats as not equal even though it is exactly the same
    new StrongQuantifier(formula, variable, selection) with ExpansionTree
  def apply(formula: HOLFormula, variable: HOLVar, selection: ExpansionTreeWithMerges): ExpansionTreeWithMerges = selection match {
    case selectionET : ExpansionTree => StrongQuantifier(formula, variable, selectionET)
    case _  => new StrongQuantifier(formula, variable, selection)
  }
  def unapply(et: ExpansionTree) = et match {
    case strongQuantifier : StrongQuantifier => Some( (strongQuantifier.formula, strongQuantifier.variable, strongQuantifier.selection.asInstanceOf[ExpansionTree]) )
    case _ => None
  }
  def unapply(et: ExpansionTreeWithMerges) = et match {
    case strongQuantifier : StrongQuantifier => Some( (strongQuantifier.formula, strongQuantifier.variable, strongQuantifier.selection) )
    case _ => None
  }
}

case class MergeNode(left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges)
  extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]]  {
  val node = None
  lazy val children = List(Pair(left, None), Pair(right, None))
}

protected[expansionTrees] class And(val left: ExpansionTreeWithMerges, val right: ExpansionTreeWithMerges)
  extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
object And {
  def apply(left: ExpansionTree, right: ExpansionTree) = new And(left, right) with ExpansionTree
  def apply(left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges): ExpansionTreeWithMerges = (left, right) match {
    case (leftET : ExpansionTree, rightET : ExpansionTree) => And(leftET, rightET)
    case _ => new And(left, right)
  }
  def unapply(et: ExpansionTree) = et match {
    case and : And => Some( (and.left.asInstanceOf[ExpansionTree], and.right.asInstanceOf[ExpansionTree]) )
    case _ => None
  }
  def unapply(et: ExpansionTreeWithMerges) = et match {
    case and : And => Some( (and.left, and.right) )
    case _ => None
  }
}

protected[expansionTrees] class Or(val left: ExpansionTreeWithMerges, val right: ExpansionTreeWithMerges)
  extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
object Or {
  def apply(left: ExpansionTree, right: ExpansionTree) = new Or(left, right) with ExpansionTree
  def apply(left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges): ExpansionTreeWithMerges = (left, right) match {
    case (leftET: ExpansionTree, rightET: ExpansionTree) => Or(leftET, rightET)
    case _ => new Or(left, right)
  }
  def unapply(et: ExpansionTree) = et match {
    case or: Or => Some((or.left.asInstanceOf[ExpansionTree], or.right.asInstanceOf[ExpansionTree]))
    case _ => None
  }
  def unapply(et: ExpansionTreeWithMerges) = et match {
    case or: Or => Some((or.left, or.right))
    case _ => None
  }
}

protected[expansionTrees] class Imp(val left: ExpansionTreeWithMerges, val right: ExpansionTreeWithMerges)
  extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
object Imp {
  def apply(left: ExpansionTree, right: ExpansionTree) = new Imp(left, right) with ExpansionTree
  def apply(left: ExpansionTreeWithMerges, right: ExpansionTreeWithMerges): ExpansionTreeWithMerges = (left, right) match {
    case (leftET : ExpansionTree, rightET : ExpansionTree) => Imp(leftET, rightET)
    case _ => new Imp(left, right)
  }
  def unapply(et: ExpansionTree) = et match {
    case imp: Imp => Some((imp.left.asInstanceOf[ExpansionTree], imp.right.asInstanceOf[ExpansionTree]))
    case _ => None
  }
  def unapply(et: ExpansionTreeWithMerges) = et match {
    case imp: Imp => Some((imp.left, imp.right))
    case _ => None
  }
}

protected[expansionTrees] class Neg(val tree: ExpansionTreeWithMerges) extends ExpansionTreeWithMerges with NonTerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(tree,None))
}
object Neg {
  def apply(tree: ExpansionTree) = new Neg(tree) with ExpansionTree
  def apply(tree: ExpansionTreeWithMerges): ExpansionTreeWithMerges = tree match {
    case treeET : ExpansionTree => Neg(treeET)
    case _ => new Neg(tree)
  }
  def unapply(et: ExpansionTree) = et match {
    case neg: Neg => Some((neg.tree).asInstanceOf[ExpansionTree])
    case _ => None
  }
  def unapply(et: ExpansionTreeWithMerges) = et match {
    case neg: Neg => Some((neg.tree))
    case _ => None
  }
}

case class Atom(formula: HOLFormula) extends ExpansionTree with TerminalNodeAWithEquality[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
}

/**
 * Returns number of quantifiers
 */
object quantRulesNumber {
  def apply(tree: ExpansionTreeWithMerges): Int = tree match {
    case Atom(f) => 0
    case Neg(t1) => quantRulesNumber(t1)
    case And(t1,t2) => quantRulesNumber(t1) + quantRulesNumber(t2)
    case Or(t1,t2) => quantRulesNumber(t1) + quantRulesNumber(t2)
    case Imp(t1,t2) => quantRulesNumber(t1) + quantRulesNumber(t2)
    case WeakQuantifier(_,children) => children.foldRight(0){
      case ((et, _), sum) => quantRulesNumber(et) + 1 + sum
    }
    case StrongQuantifier(_,_,et) => quantRulesNumber(et) + 1
  }

  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : Int = {
    val qAnt = ep._1.foldLeft(0)( (sum, et) => quantRulesNumber(et) + sum)
    val qSuc = ep._2.foldLeft(0)( (sum, et) => quantRulesNumber(et) + sum)
    qAnt + qSuc
  }
}


// TODO:
class ExpansionSequent(antecedent: Seq[ExpansionTreeWithMerges], succedent: Seq[ExpansionTreeWithMerges]) { }


object toDeep {
  def apply(tree: ExpansionTreeWithMerges): HOLFormula = tree match {
    case Atom(f) => f
    case Neg(t1) => NegHOL(toDeep(t1))
    case And(t1,t2) => AndHOL(toDeep(t1), toDeep(t2))
    case Or(t1,t2) => OrHOL(toDeep(t1), toDeep(t2))
    case Imp(t1,t2) => ImpHOL(toDeep(t1), toDeep(t2))
    case WeakQuantifier(_,cs) => OrHOL( cs.map( t => toDeep(t._1)).toList )
    case StrongQuantifier(_,_,t) => toDeep(t)
  }
}

// Daniel: shouldn't this rather be called toShallow to keep in line
// with expansion tree terminology? toFormula is IMHO confusing since
// there are two formulas (Deep and Shallow) associated to ever 
// expansion tree.
object toFormula {
  def apply(tree: ExpansionTreeWithMerges): HOLFormula = tree match {
    case Atom(f) => f
    case Neg(t1) => NegHOL(toFormula(t1))
    case And(t1,t2) => AndHOL(toFormula(t1), toFormula(t2))
    case Or(t1,t2) => OrHOL(toFormula(t1), toFormula(t2))
    case Imp(t1,t2) => ImpHOL(toFormula(t1), toFormula(t2))
    case WeakQuantifier(f,_) => f
    case StrongQuantifier(f,_,_) => f
  }
}

// Returns the end-sequent of the proof represented by this expansion tree
object toSequent {
  def apply(ep: (Seq[ExpansionTree], Seq[ExpansionTree])) : Sequent = {
    // TODO: there MUST be an easier way...
    val ant = ep._1.map( et => defaultFormulaOccurrenceFactory.createFormulaOccurrence(toFormula(et), Nil) )
    val cons = ep._2.map( et => defaultFormulaOccurrenceFactory.createFormulaOccurrence(toFormula(et), Nil) )

    Sequent(ant, cons)
  }
}

// Builds an expansion tree given a quantifier free formula
object qFreeToExpansionTree {
  def apply(f : HOLFormula) : ExpansionTree = f match {
    case AtomHOL(_,_) => Atom(f)
    case NegHOL(f) => Neg(qFreeToExpansionTree(f)).asInstanceOf[ExpansionTree]
    case AndHOL(f1,f2) => And(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2)).asInstanceOf[ExpansionTree]
    case OrHOL(f1,f2) => Or(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2)).asInstanceOf[ExpansionTree]
    case ImpHOL(f1,f2) => Imp(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2)).asInstanceOf[ExpansionTree]
    case _ => throw new Exception("Error transforming a quantifier-free formula into an expansion tree: " + f)
  }
}

// Builds an expansion tree given a *prenex* formula and 
// its instances (or substitutions) using only weak quantifiers. 
//
// NOTE: initially, this could be implemented for non-prenex formulas. 
// What needs to be implemented is a method to remove the quantifiers of a
// non-prenex formula (taking care about the renaming of variables).
object prenexToExpansionTree {
  def apply(f: HOLFormula, lst: List[HOLFormula]) : ExpansionTree = {
    val fMatrix = f.getMatrix

    // Each possible instance will generate an expansion tree, and they all 
    // have the same root.
    val children = lst.foldLeft(List[(ExpansionTreeWithMerges, HOLExpression)]()) {
      case (acc, instance) =>
        val subs = NaiveIncompleteMatchingAlgorithm.matchTerm(fMatrix, instance)
        val expTree = subs match {
          case Some(sub) => apply_(f, sub) 
          case None => throw new Exception("ERROR: prenexToExpansionTree: No substitutions found for:\n" + 
            "Matrix: " + fMatrix + "\nInstance: " + instance)
        }
        expTree match {
          case WeakQuantifier(_, lst) => lst.toList ++ acc
          case _ => throw new Exception("ERROR: Quantifier-free formula?")
        }
    }
    
    // TODO: merge edges with the same term.
    WeakQuantifier(f, children).asInstanceOf[ExpansionTree] // can't contain merges currently, c.f. TODO above
  }

  def apply_(f: HOLFormula, sub: Substitution[HOLExpression]) : ExpansionTreeWithMerges = f match {
    case AllVar(v, form) => 
      val t = sub.getTerm(v)
      val one_sub = Substitution[HOLExpression](v, t)
      val newf = one_sub(form).asInstanceOf[HOLFormula]
      //val newf = f.instantiate(t.asInstanceOf[FOLTerm])
      WeakQuantifier(f, List(Pair(apply_(newf, sub), t)))
    case ExVar(v, form) => 
      val t = sub.getTerm(v)
      val one_sub = Substitution[HOLExpression](v, t)
      val newf = one_sub(form).asInstanceOf[HOLFormula]
      //val newf = f.instantiate(t.asInstanceOf[FOLTerm])
      WeakQuantifier(f, List(Pair(apply_(newf, sub), t)))
    case _ => qFreeToExpansionTree(f)
  }
  
}

/**
 * Returns the expansion sequent with certain expansions trees removed
 */
object removeFromExpansionSequent {
  /**
   * @param seq: specifies formulas to remove; formulas in the antecedent/consequent will remove expansion trees in the antecedent/consequent of the expansion tree
   *             expansion trees are removed if Sh(e) \in seq (using default equality, which is alpha equality)
   */
  def apply(etSeq: (Seq[ExpansionTree], Seq[ExpansionTree]), seq: FSequent) :  (Seq[ExpansionTree], Seq[ExpansionTree]) = {
    val ante = etSeq._1.filter( et => ! seq._1.contains( toFormula(et) ) )
    val cons = etSeq._2.filter( et => ! seq._2.contains( toFormula(et) ) )
    (ante, cons)
  }
}

/**
 * Applies a function to all expansion trees in an expansion sequent
 * TODO: Implement proper handling of expansion sequents (special class like Sequent?)
 */
object applyToExpansionSequent {
  def apply[T](fun: ExpansionTree => T, etSeq: (Seq[ExpansionTree], Seq[ExpansionTree])) : (Seq[T], Seq[T]) = {
    (etSeq._1.map(fun), etSeq._2.map(fun))
  }
}


object substitute {
  /**
   * Perform substitution including propagation of merge nodes
   */
  def apply(s: Substitution[HOLExpression], et: ExpansionTreeWithMerges): ExpansionTree = {
    val etSubstituted = doApplySubstitution(s, et)
    propagateMerges(etSubstituted)
  }

  /**
   * Perform substitution _without_ propagation of merge nodes
   * Useful for tests, has to be extra method due to different return type
   */
  def applyNoMerge(s: Substitution[HOLExpression], et: ExpansionTreeWithMerges): ExpansionTreeWithMerges = {
    doApplySubstitution(s, et)
  }

  private[expansionTrees] def doApplySubstitution(s: Substitution[HOLExpression], et: ExpansionTreeWithMerges): ExpansionTreeWithMerges = et match {
    case Atom(f) => Atom(s.apply(f).asInstanceOf[HOLFormula])
    case Neg(t1) => Neg(doApplySubstitution(s, t1))
    case And(t1,t2) => And(doApplySubstitution(s, t1), doApplySubstitution(s, t2))
    case Or(t1,t2) => Or(doApplySubstitution(s, t1), doApplySubstitution(s, t2))
    case Imp(t1,t2) => Imp(doApplySubstitution(s, t1), doApplySubstitution(s, t2))
    case StrongQuantifier(f, v, selection) =>
      StrongQuantifier(s.apply(f).asInstanceOf[HOLFormula], s.apply(v).asInstanceOf[HOLVar], doApplySubstitution(s, selection))
    case WeakQuantifier(f, instances) =>
      WeakQuantifier(s.apply(f).asInstanceOf[HOLFormula], mergeWeakQuantifiers(s, instances) )
    case MergeNode(t1, t2) => MergeNode(doApplySubstitution(s, t1), doApplySubstitution(s, t2))
  }

  private[expansionTrees] def mergeWeakQuantifiers(s: Substitution[HOLExpression], instances: Seq[(ExpansionTreeWithMerges, HOLExpression)]): Seq[(ExpansionTreeWithMerges, HOLExpression)] = {
    // through merging, some instances might disappear
    // keep map (substituted var -> [  ] ) to rebuild instances from it
    type InstList = ListBuffer[ExpansionTreeWithMerges]
    var newInstances = collection.mutable.Map[HOLExpression, InstList]()
    instances.foreach({ case (et, expr) =>  (newInstances.getOrElseUpdate(s.apply(expr), new InstList) += doApplySubstitution(s, et)) })

    def createMergeNode(ets: Iterable[ExpansionTreeWithMerges]): ExpansionTreeWithMerges = {
      ets.reduce( (tree1, tree2) => MergeNode(tree1, tree2) )
    }

    newInstances.map(instance => (createMergeNode(instance._2), instance._1)).toList
  }
}

object propagateMerges {
  def apply(etMerge: ExpansionTreeWithMerges): ExpansionTree = etMerge.asInstanceOf[ExpansionTree] // TODO
}



