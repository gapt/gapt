package at.logic.calculi.expansionTrees

import at.logic.language.hol._
import at.logic.language.fol.{FOLFormula, FOLTerm, FOLExpression}
import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL}
import at.logic.utils.ds.trees._
import at.logic.language.lambda.substitutions._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._

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
        // WARNING: Considering only the first substitution
        val expTree = subs match {
          case h::t => apply_(f, h) // WARNING: considering only the first substitution
          case Nil => throw new Exception("ERROR: prenexToExpansionTree: No substitutions found for:\n" + 
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

  def apply_(f: FOLFormula, sub: Substitution[FOLExpression]) : ExpansionTree = f match {
    case AllVar(v, _) => //v What is this 'v' doing here?
      val t = sub.getTerm(v)
      val newf = f.instantiate(t.asInstanceOf[FOLTerm])
      WeakQuantifier(f, List(Pair(apply_(newf, sub), t)))
    case ExVar(v, _) => //v
      val t = sub.getTerm(v)
      val newf = f.instantiate(t.asInstanceOf[FOLTerm])
      WeakQuantifier(f, List(Pair(apply_(newf, sub), t)))
    case _ => qFreeToExpansionTree(f)
  }
  
}
