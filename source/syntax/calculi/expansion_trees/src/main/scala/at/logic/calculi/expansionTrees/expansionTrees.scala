package at.logic.calculi.expansionTrees

import at.logic.language.hol._
import at.logic.language.fol.{FOLFormula, FOLTerm, FOLExpression}
import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL}
import at.logic.utils.ds.trees._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm

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

// Builds an expansion tree given a quantifier free formula
object qFreeToExpansionTree {
  def apply(f : HOLFormula) : ExpansionTree= f match {
    case AtomHOL(_,_) => Atom(f)
    case Neg(f) => Not(qFreeToExpansionTree(f))
    case AndHOL(f1,f2) => And(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case OrHOL(f1,f2) => Or(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case ImpHOL(f1,f2) => Imp(qFreeToExpansionTree(f1), qFreeToExpansionTree(f2))
    case _ => throw new Exception("Error transforming a quantifier-free formula into an expansion tree")
  }
}

// Builds an expansion tree given a *prenex first order* formula and 
// its instances (or substitutions) using only weak quantifiers. 
//
// NOTE: initially, this could be implemented for non-prenex formulas in HOL. 
// What needs to be implemented is a method to remove the quantifiers of a
// non-prenex formula (taking care about the renaming of variables) and a
// matching that would return the substitutions (there is a HOL matching
// implemented, but it is called NaiveIncompleteMatchingAlgorithm, and I am not
// sure whether I trust this name :P ).
object prenexToExpansionTree {
  def apply(f: FOLFormula, lst: List[FOLFormula]) : ExpansionTree = {
    val fMatrix = f.getMatrix

    // Each possible instance will generate an expansion tree, and they all 
    // have the same root.
    val children = lst.foldLeft(List[(ExpansionTree, HOLExpression)]()) { 
      case (acc, instance) => 
        val subs = FOLUnificationAlgorithm.unify(fMatrix, instance)
        val expTree = apply_(f, subs)
        expTree match {
          case WeakQuantifier(_, lst) => lst.toList ++ acc
          case _ => throw new Exception("ERROR: Quantifier-free formula?")
        }
    }
    
    // TODO: merge edges with the same term.
    WeakQuantifier(f, children)
  }

  def apply_(f: FOLFormula, subs: List[Substitution[FOLExpression]]) : ExpansionTree = subs match {
    case sub :: tail =>
      val term = sub.getTerm
      val newf = sub(f).asInstanceOf[FOLFormula] 
      WeakQuantifier(f, List(Pair(apply_(newf, tail), term)))

    case Nil => qFreeToExpansionTree(f)
  }
}
