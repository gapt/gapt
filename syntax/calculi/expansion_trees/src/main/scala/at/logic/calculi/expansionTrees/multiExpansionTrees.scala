package at.logic.calculi.expansionTrees

import at.logic.language.hol._
import at.logic.utils.ds.trees._

/**
 * These trees are the same as expansion trees but consider sequential quantifiers of the same type as quantification over a vector of
 * variables. I.e. an expansion tree having two strong qantifiers over x and y will have a StrongQuantifer child over x and a Strong
 * Quantifier grandchild over y while a multi expansion tree over the same formula will have only StrongQuantifier child over the vector
 * <x,y>
 */
object multi {

type T1 = NonTerminalNodeA[Option[HOLFormula],Option[Seq[HOLExpression]]]

trait MultiExpansionTree extends TreeA[Option[HOLFormula],Option[Seq[HOLExpression]]]

case class WeakQuantifier(formula: HOLFormula, instances: Seq[Tuple2[MultiExpansionTree, Seq[HOLExpression]]])
  extends MultiExpansionTree with T1 {
    lazy val node = Some(formula)
    lazy val children = instances.map(x => (x._1,Some(x._2)))
  }
case class StrongQuantifier(formula: HOLFormula, variables: Seq[HOLVar], selection: MultiExpansionTree)
  extends MultiExpansionTree with T1 {
  lazy val node = Some(formula)
  lazy val children = List((selection, Some(variables)))
}

case class And(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Or(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Imp(left: MultiExpansionTree, right: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Pair(left,None),Pair(right,None))
}
case class Not(tree: MultiExpansionTree) extends MultiExpansionTree with T1 {
  val node = None
  lazy val children = List(Pair(tree,None))
}
case class Atom(formula: HOLFormula) extends MultiExpansionTree with TerminalNodeA[Option[HOLFormula],Option[Seq[HOLExpression]]] {
  lazy val node = Some(formula)
}
}
