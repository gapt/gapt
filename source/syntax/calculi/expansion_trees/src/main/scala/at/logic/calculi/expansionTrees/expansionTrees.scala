package at.logic.calculi.expansionTrees

import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, _}
import at.logic.utils.ds.trees._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.matching.hol._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.types.FSequent

trait ExpansionTree extends TreeA[Option[HOLFormula],Option[HOLExpression]]

case class WeakQuantifier(formula: HOLFormula, instances: Seq[Tuple2[ExpansionTree, HOLExpression]])
  extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = instances.map(x => (x._1,Some(x._2)))
}

case class StrongQuantifier(formula: HOLFormula, variable: HOLVar, selection: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
  lazy val children = List(Pair(selection,Some(variable)))
}

case class And(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Or(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Imp(left: ExpansionTree, right: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Not(tree: ExpansionTree) extends ExpansionTree with NonTerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  val node = None
  lazy val children = List(Pair(tree,None))
}
case class Atom(formula: HOLFormula) extends ExpansionTree with TerminalNodeA[Option[HOLFormula],Option[HOLExpression]] {
  lazy val node = Some(formula)
}

object quantRulesNumber {
  def apply(tree: ExpansionTree): Int = tree match {
    case Atom(f) => 0
    case Not(t1) => quantRulesNumber(t1)
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

object toDeep {
  def apply(tree: ExpansionTree): HOLFormula = tree match {
    case Atom(f) => f
    case Not(t1) => Neg(toDeep(t1))
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
  def apply(tree: ExpansionTree): HOLFormula = tree match {
    case Atom(f) => f
    case Not(t1) => Neg(toFormula(t1))
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
  def apply(f : HOLFormula) : ExpansionTree= f match {
    case AtomHOL(_,_) => Atom(f)
    case Neg(f) => Not(qFreeToExpansionTree(f))
    case AndHOL(f1,f2) => And(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case OrHOL(f1,f2) => Or(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case ImpHOL(f1,f2) => Imp(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
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
    val children = lst.foldLeft(List[(ExpansionTree, HOLExpression)]()) { 
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
    WeakQuantifier(f, children)
  }

  def apply_(f: HOLFormula, sub: Substitution[HOLExpression]) : ExpansionTree = f match {
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

